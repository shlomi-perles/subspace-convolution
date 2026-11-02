#!/usr/bin/env bash
# Second campaign, part b (socket 0, after run_phase4.sh):
#   3. larger tables of F_9 and F_5 with every covering pair stored (longest first);
#   4. Grassmann kernels with larger [k]_q.
# Each job is claimed (mkdir in $CLAIMS) before it starts, so a second copy started
# on socket 1 once run_phase2.sh is done, with its own OUT and BDIR, runs the jobs
# socket 0 has not reached.
# Every timed run is single-threaded; index construction uses $OMP_NUM_THREADS.
#
# usage:  nohup numactl --cpunodebind=0 bash scripts/run_phase2b.sh > run_phase2b.log 2>&1 &
#         OUT=results_phase2b_n1 BDIR=build_c nohup numactl --cpunodebind=1 bash scripts/run_phase2b.sh > run_phase2b_n1.log 2>&1 &
#         tail -f results_phase2b/progress.log
set -uo pipefail
cd "$(dirname "$0")/.."
OUT=${OUT:-results_phase2b}
B=${BDIR:-build_b}
CLAIMS=${CLAIMS:-claims_phase2b}
mkdir -p "$OUT" "$CLAIMS"
log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/progress.log"; }

{ date -u; uname -a; lscpu; free -g; numactl --show 2>/dev/null; g++ --version | head -1
  cmake --version | head -1; echo "OMP_NUM_THREADS=${OMP_NUM_THREADS:-unset}"; } > "$OUT/environment.txt" 2>&1
git rev-parse HEAD > "$OUT/commit.txt" 2>/dev/null || true

if ! { cmake -S . -B "$B" -DCMAKE_BUILD_TYPE=Release >/dev/null && cmake --build "$B" -j"$(nproc)" >/dev/null; }; then
  log "STOP: build failed"; exit 1
fi
if ctest --test-dir "$B" > "$OUT/ctest.log" 2>&1; then log "unit tests passed"; else log "WARNING: unit tests FAILED"; fi

echo "case,exit_code,peak_rss_gb,seconds" > "$OUT/runs.csv"
run() {  # run one benchmark unless the other socket took it; record exit code, peak memory and duration; never abort
  local name=$1; shift
  if ! mkdir "$CLAIMS/$name" 2>/dev/null; then log "skip  $name: taken by the other socket"; return; fi
  log "start $name"
  local t0=$SECONDS rc rss="NA"
  /usr/bin/time -f "%M" -o "$OUT/.rss" "$@" >> "$OUT/bench.log" 2>&1; rc=$?
  rss=$(tail -n 1 "$OUT/.rss" 2>/dev/null | awk '{printf "%.2f", $1 / 1048576}')
  echo "$name,$rc,$rss,$(( SECONDS - t0 ))" >> "$OUT/runs.csv"
  log "end   $name: exit $rc, peak $rss GB, $(( SECONDS - t0 )) s"
}

# 3. Full transform, larger tables of F_9 and F_5 with every covering pair stored.
run paired_q9_n6 $B/bench_paired --q 9 --nmin 6 --nmax 6 --rounds 3 --out "$OUT/paired.csv"
run paired_q5_n7 $B/bench_paired --q 5 --nmin 7 --nmax 7 --rounds 3 --out "$OUT/paired.csv"

# 4. Grassmann kernels with larger [k]_q.
run kernel_8_6_3 $B/bench_grassmann --part kernel --q 8 --n 6 --k 3 --graph-gb 300 --out "$OUT/grassmann.csv"
run kernel_3_8_4 $B/bench_grassmann --part kernel --q 3 --n 8 --k 4 --graph-gb 300 --out "$OUT/grassmann.csv"

# 5. Poisson summation for I_6^{2,4} over F_8 (550 GB table), the one incidence instance whose
#    alternative fits in memory but is not in run_phase2.sh.
run poisson_8_6_2_4 $B/bench_poisson --q 8 --n 6 --a 2 --b 4 --samples 200 --out "$OUT/poisson.csv"

rm -f "$OUT/.rss"
tar czf "$OUT.tar.gz" "$OUT"
log "DONE"
