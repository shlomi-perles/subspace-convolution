#!/usr/bin/env bash
# Third campaign: the full transform over F_32 (5-bit coordinates), where the
# covering pairs of F_32^5 (1.25e12, about 5 TB) can only be timed on a sample,
# and a check of the sampled estimate against the full runs of run_bigmem.sh on
# the two largest tables whose pairs fit (F_8^6, F_16^5).
#
# usage:  nohup numactl --cpunodebind=0 bash scripts/run_phase3.sh > run_phase3.log 2>&1 &
set -uo pipefail
cd "$(dirname "$0")/.."
OUT=results_phase3
mkdir -p "$OUT"
log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/progress.log"; }
{ date -u; uname -a; lscpu; free -g; numactl --show 2>/dev/null; g++ --version | head -1
  echo "OMP_NUM_THREADS=${OMP_NUM_THREADS:-unset}"; } > "$OUT/environment.txt" 2>&1
git rev-parse HEAD > "$OUT/commit.txt" 2>/dev/null || true

for bits in 4 5; do
  if ! { cmake -S . -B build$bits -DCMAKE_BUILD_TYPE=Release -DFSC_COORD_BITS=$bits >/dev/null &&
         cmake --build build$bits -j"$(nproc)" >/dev/null; }; then
    log "STOP: build ($bits bits) failed"; exit 1
  fi
done
if ctest --test-dir build5 > "$OUT/ctest5.log" 2>&1; then log "unit tests (5-bit build, includes q=32) passed"
else log "WARNING: unit tests FAILED"; fi

echo "case,exit_code,peak_rss_gb,seconds" > "$OUT/runs.csv"
run() {
  local name=$1; shift
  log "start $name"
  local t0=$SECONDS rc rss="NA"
  /usr/bin/time -f "%M" -o "$OUT/.rss" "$@" >> "$OUT/bench.log" 2>&1; rc=$?
  rss=$(tail -n 1 "$OUT/.rss" 2>/dev/null | awk '{printf "%.2f", $1 / 1048576}')
  echo "$name,$rc,$rss,$(( SECONDS - t0 ))" >> "$OUT/runs.csv"
  log "end   $name: exit $rc, peak $rss GB, $(( SECONDS - t0 )) s"
}

run paired_q32_small build5/bench_paired --q 32 --nmin 3 --nmax 4 --rounds 11 --out "$OUT/paired.csv"
run paired_q32_n5 build5/bench_paired --q 32 --nmin 5 --nmax 5 --rounds 3 --sample 0.02 --out "$OUT/paired.csv"
run sampled_q16_n5 build4/bench_paired --q 16 --nmin 5 --nmax 5 --rounds 3 --sample 0.02 --out "$OUT/paired_sampled.csv"
run sampled_q8_n6 build4/bench_paired --q 8 --nmin 6 --nmax 6 --rounds 3 --sample 0.02 --out "$OUT/paired_sampled.csv"

rm -f "$OUT/.rss"
tar czf results_phase3.tar.gz "$OUT"
log "DONE"
