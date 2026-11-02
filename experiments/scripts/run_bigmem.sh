#!/usr/bin/env bash
# First campaign: the full transform for every field, the incidence table and the
# Grassmann kernels, on ONE machine with enough memory to store all covering
# pairs (no sampling). Needs at least
# 200 GB of RAM available to this container (the full covering-pair index of
# F_8^6 is about 100 GB and its construction can briefly need about twice that).
# Takes about 2-3 hours. Results: results_bigmem.tar.gz in the repository root.
#
# usage:  nohup bash scripts/run_bigmem.sh > run_bigmem.log 2>&1 &
#         tail -f results_bigmem/progress.log
# test:   SMOKE=1 bash scripts/run_bigmem.sh      (small sizes, a few minutes)
set -uo pipefail
cd "$(dirname "$0")/.."
SMOKE=${SMOKE:-0}
OUT=results_bigmem
mkdir -p "$OUT"
log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/progress.log"; }

# 1. Memory available to this container: host RAM or cgroup limit, whichever is lower.
mem_kb=$(awk '/MemAvailable/ {print $2}' /proc/meminfo)
lim=$(cat /sys/fs/cgroup/memory.max 2>/dev/null || cat /sys/fs/cgroup/memory/memory.limit_in_bytes 2>/dev/null || echo max)
if [[ $lim =~ ^[0-9]+$ ]] && (( lim / 1024 < mem_kb )); then mem_kb=$(( lim / 1024 )); fi
mem_gb=$(( mem_kb / 1048576 ))
need_gb=${NEED_GB:-200}
(( SMOKE == 1 )) && need_gb=2
if (( mem_gb < need_gb )); then
  log "STOP: only $mem_gb GB available to this container; need $need_gb GB"
  exit 1
fi
log "memory available: $mem_gb GB"

# 2. Toolchain (Debian/Ubuntu images; root or sudo).
if ! command -v cmake >/dev/null || ! command -v g++ >/dev/null || [[ ! -x /usr/bin/time ]]; then
  SUDO=""; [[ $(id -u) != 0 ]] && SUDO=sudo
  export DEBIAN_FRONTEND=noninteractive
  log "installing build-essential, cmake, time"
  $SUDO apt-get update -qq >/dev/null && $SUDO apt-get install -y -qq build-essential cmake time >/dev/null \
    || log "WARNING: apt-get failed"
fi
{ date -u; uname -a; lscpu; free -g; echo "cgroup memory limit: $lim"; g++ --version | head -1
  cmake --version | head -1; } > "$OUT/environment.txt" 2>&1

# 3. Build and run the unit tests (exact checks against direct summation).
if ! { cmake -S . -B build -DCMAKE_BUILD_TYPE=Release >/dev/null && cmake --build build -j"$(nproc)" >/dev/null; }; then
  log "STOP: build failed"; exit 1
fi
if ctest --test-dir build > "$OUT/ctest.log" 2>&1; then log "unit tests passed"; else log "WARNING: unit tests FAILED, see $OUT/ctest.log"; fi

B=build
P=$B/bench_paired
echo "case,exit_code,peak_rss_gb,seconds" > "$OUT/runs.csv"
run() {  # run one benchmark; record exit code, peak memory and duration; never abort the script
  local name=$1; shift
  log "start $name"
  local t0=$SECONDS rc rss="NA"
  if [[ -x /usr/bin/time ]]; then
    /usr/bin/time -f "%M" -o "$OUT/.rss" "$@" >> "$OUT/bench.log" 2>&1; rc=$?
    rss=$(tail -n 1 "$OUT/.rss" 2>/dev/null | awk '{printf "%.2f", $1 / 1048576}')
  else
    "$@" >> "$OUT/bench.log" 2>&1; rc=$?
  fi
  echo "$name,$rc,$rss,$(( SECONDS - t0 ))" >> "$OUT/runs.csv"
  log "end   $name: exit $rc, peak $rss GB, $(( SECONDS - t0 )) s"
}

if (( SMOKE == 1 )); then
  run paired_q2 $P --q 2 --nmin 4 --nmax 6 --rounds 3 --out "$OUT/paired.csv"
  run paired_q8 $P --q 8 --nmin 3 --nmax 4 --rounds 3 --out "$OUT/paired.csv"
  run paired_q7 $P --q 7 --nmin 3 --nmax 3 --rounds 3 --out "$OUT/paired.csv"
  run incidence $B/bench_incidence_hard --only 2:8:2:6 --samples 20 --out "$OUT/incidence_hard.csv"
  run kernel_2_6_3 $B/bench_grassmann --part kernel --q 2 --n 6 --k 3 --graph-gb 64 --out "$OUT/grassmann.csv"
  run verify $B/verify_large --smoke 1 --out "$OUT/verify_large.csv"
else
  # Full transform: paired rounds for every field and size, covering pairs stored in full.
  run paired_q2  $P --q 2  --nmin 4 --nmax 9 --rounds 21 --out "$OUT/paired.csv"
  run paired_q3  $P --q 3  --nmin 4 --nmax 7 --rounds 21 --out "$OUT/paired.csv"
  run paired_q4  $P --q 4  --nmin 4 --nmax 6 --rounds 21 --out "$OUT/paired.csv"
  run paired_q5  $P --q 5  --nmin 4 --nmax 6 --rounds 21 --out "$OUT/paired.csv"
  run paired_q8  $P --q 8  --nmin 3 --nmax 5 --rounds 21 --out "$OUT/paired.csv"
  run paired_q16 $P --q 16 --nmin 3 --nmax 4 --rounds 21 --out "$OUT/paired.csv"
  run paired_q9  $P --q 9  --nmin 3 --nmax 5 --rounds 21 --out "$OUT/paired.csv"
  run paired_q7  $P --q 7  --nmin 3 --nmax 5 --rounds 21 --out "$OUT/paired.csv"
  run paired_q11 $P --q 11 --nmin 3 --nmax 5 --rounds 11 --out "$OUT/paired.csv"
  run paired_q13 $P --q 13 --nmin 3 --nmax 5 --rounds 11 --out "$OUT/paired.csv"
  # Incidence table (times; the operation counts do not depend on the machine).
  run incidence $B/bench_incidence_hard --samples 200 --out "$OUT/incidence_hard.csv"
  # Grassmann kernels, now with room for the factored recurrence on Gr_2(10,5).
  for nk in "2 4 2" "2 6 3" "2 8 4" "2 10 5" "3 4 2" "3 6 3" "4 4 2" "4 6 3" "5 4 2" "5 6 3"; do
    set -- $nk
    run "kernel_$1_$2_$3" $B/bench_grassmann --part kernel --q "$1" --n "$2" --k "$3" --graph-gb 64 --out "$OUT/grassmann.csv"
  done
  # The largest tables, smallest covering-pair index first (12, 22, 22, 27, 34, 93 GB).
  run paired_q4_n7  $P --q 4  --nmin 7  --nmax 7  --rounds 11 --out "$OUT/paired.csv"
  run paired_q16_n5 $P --q 16 --nmin 5  --nmax 5  --rounds 11 --out "$OUT/paired.csv"
  run paired_q7_n6  $P --q 7  --nmin 6  --nmax 6  --rounds 7  --out "$OUT/paired.csv"
  run paired_q3_n8  $P --q 3  --nmin 8  --nmax 8  --rounds 7  --out "$OUT/paired.csv"
  run paired_q2_n10 $P --q 2  --nmin 10 --nmax 10 --rounds 7  --out "$OUT/paired.csv"
  run paired_q8_n6  $P --q 8  --nmin 6  --nmax 6  --rounds 7  --out "$OUT/paired.csv"
  # Direct summation at random positions of the largest outputs.
  run verify $B/verify_large --samples 400 --out "$OUT/verify_large.csv"
fi

rm -f "$OUT/.rss"
tar czf results_bigmem.tar.gz "$OUT"
log "DONE. Download results_bigmem.tar.gz ($(du -h results_bigmem.tar.gz | cut -f1)) and send it back."
