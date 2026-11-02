#!/usr/bin/env bash
# Second campaign for a machine with >= 1 TB of RAM (run after run_bigmem.sh):
#   1. the incidence table with the new instances, I^{2,5}_7 over F_8 (S = 2.5e9)
#      among them, running the covering-pair algorithm wherever its index fits;
#   2. Poisson summation, the best alternative on most incidence rows, run on
#      every row where its table fits (up to 550 GB);
#   (3. and 4. are in scripts/run_phase2b.sh, run on the other socket.)
# Every timed run is single-threaded; index construction uses $OMP_NUM_THREADS.
#
# usage:  nohup numactl --cpunodebind=1 bash scripts/run_phase2.sh > run_phase2.log 2>&1 &
#         tail -f results_phase2/progress.log
set -uo pipefail
cd "$(dirname "$0")/.."
OUT=results_phase2
mkdir -p "$OUT"
log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/progress.log"; }

{ date -u; uname -a; lscpu; free -g; numactl --show 2>/dev/null; g++ --version | head -1
  cmake --version | head -1; echo "OMP_NUM_THREADS=${OMP_NUM_THREADS:-unset}"; } > "$OUT/environment.txt" 2>&1
git rev-parse HEAD > "$OUT/commit.txt" 2>/dev/null || true

if ! { cmake -S . -B build -DCMAKE_BUILD_TYPE=Release >/dev/null && cmake --build build -j"$(nproc)" >/dev/null; }; then
  log "STOP: build failed"; exit 1
fi
if ctest --test-dir build > "$OUT/ctest.log" 2>&1; then log "unit tests passed"; else log "WARNING: unit tests FAILED"; fi

B=build
echo "case,exit_code,peak_rss_gb,seconds" > "$OUT/runs.csv"
run() {  # run one benchmark; record exit code, peak memory and duration; never abort
  local name=$1; shift
  log "start $name"
  local t0=$SECONDS rc rss="NA"
  /usr/bin/time -f "%M" -o "$OUT/.rss" "$@" >> "$OUT/bench.log" 2>&1; rc=$?
  rss=$(tail -n 1 "$OUT/.rss" 2>/dev/null | awk '{printf "%.2f", $1 / 1048576}')
  echo "$name,$rc,$rss,$(( SECONDS - t0 ))" >> "$OUT/runs.csv"
  log "end   $name: exit $rc, peak $rss GB, $(( SECONDS - t0 )) s"
}

# 1. Incidence table, all instances; covering-pair algorithm where its index fits in 400 GB.
run incidence $B/bench_incidence_hard --samples 200 --sweep-gb 400 --out "$OUT/incidence_hard.csv"

# 2. Poisson summation, smallest table first (the last two need 550 GB each).
for c in "2 16 1 15" "2 8 2 6" "2 12 2 10" "2 13 2 11" "2 14 2 12" "3 8 2 6" "3 9 2 7" "2 9 3 6" "4 7 2 5" \
         "2 10 3 7" "4 8 2 6" "2 11 3 8" "4 9 2 7" "2 12 3 9"; do
  set -- $c
  run "poisson_$1_$2_$3_$4" $B/bench_poisson --q "$1" --n "$2" --a "$3" --b "$4" --samples 200 --out "$OUT/poisson.csv"
done

# 3-4. Grassmann kernels and F_5^7, F_9^6: scripts/run_phase2b.sh (other socket).

rm -f "$OUT/.rss"
tar czf results_phase2.tar.gz "$OUT"
log "DONE"
