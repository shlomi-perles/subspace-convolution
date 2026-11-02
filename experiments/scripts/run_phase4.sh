#!/usr/bin/env bash
# Fourth campaign: prime fields q = 7, 11, 13 again, now with the paired
# length-p DFT kernel (arith.hpp); every covering pair stored.
# usage:  nohup numactl --cpunodebind=0 bash scripts/run_phase4.sh > run_phase4.log 2>&1 &
set -uo pipefail
cd "$(dirname "$0")/.."
OUT=results_phase4
mkdir -p "$OUT"
log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/progress.log"; }
{ date -u; lscpu | head -20; numactl --show 2>/dev/null; echo "OMP_NUM_THREADS=${OMP_NUM_THREADS:-unset}"; } > "$OUT/environment.txt" 2>&1
git rev-parse HEAD > "$OUT/commit.txt" 2>/dev/null || true
if ! { cmake -S . -B build -DCMAKE_BUILD_TYPE=Release >/dev/null && cmake --build build -j"$(nproc)" >/dev/null; }; then
  log "STOP: build failed"; exit 1
fi
if ctest --test-dir build > "$OUT/ctest.log" 2>&1; then log "unit tests passed"; else log "WARNING: unit tests FAILED"; fi
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
B=build/bench_paired
run paired_q7  $B --q 7  --nmin 3 --nmax 5 --rounds 21 --out "$OUT/paired.csv"
run paired_q11 $B --q 11 --nmin 3 --nmax 5 --rounds 11 --out "$OUT/paired.csv"
run paired_q13 $B --q 13 --nmin 3 --nmax 5 --rounds 11 --out "$OUT/paired.csv"
run paired_q7_n6 $B --q 7 --nmin 6 --nmax 6 --rounds 7 --out "$OUT/paired.csv"
rm -f "$OUT/.rss"
tar czf results_phase4.tar.gz "$OUT"
log "DONE"
