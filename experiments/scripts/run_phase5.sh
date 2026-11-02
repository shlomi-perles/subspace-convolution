#!/usr/bin/env bash
# Fifth campaign: correctness of every table timed by bench_paired (which only
# times) and of the Grassmann kernels.  For each q:n:t in CASES4 (4-bit build) and
# CASES5 (5-bit build, q = 32): direct zeta and Mobius sums at random positions, the
# hybrid (threshold t) against the recursion on all entries, and the covering-pair
# algorithm against the recursion on all entries, both directions, where its index
# fits in 400 GB (all but F_32^5).  For each q:n:k in KCASES (4-bit build): K f by
# direct summation at random centers, and Algorithm 3 with covering-pair transforms
# on all entries.  The engine (include/fsc) is the one of the timed runs: unchanged
# since 0b700a4 apart from the 5-bit refactoring.  Run on a socket whose timed jobs
# are done.
#
# usage:  CASES4=9:6:4,8:6:4 CASES5=32:5:3 KCASES=8:6:3 OUT=results_phase5_n1 BDIR=build_v1 \
#           nohup numactl --cpunodebind=1 bash scripts/run_phase5.sh > run_phase5_n1.log 2>&1 &
set -uo pipefail
cd "$(dirname "$0")/.."
OUT=${OUT:-results_phase5}
B=${BDIR:-build_v}
CASES4=${CASES4:-}
CASES5=${CASES5:-}
KCASES=${KCASES:-}
mkdir -p "$OUT"
log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/progress.log"; }

{ date -u; uname -a; lscpu; free -g; numactl --show 2>/dev/null; g++ --version | head -1
  cmake --version | head -1; echo "OMP_NUM_THREADS=${OMP_NUM_THREADS:-unset}"; } > "$OUT/environment.txt" 2>&1
git rev-parse HEAD > "$OUT/commit.txt" 2>/dev/null || true

for bits in 4 5; do
  [[ $bits == 4 && -z $CASES4$KCASES || $bits == 5 && -z $CASES5 ]] && continue
  if ! { cmake -S . -B "$B$bits" -DCMAKE_BUILD_TYPE=Release -DFSC_COORD_BITS=$bits >/dev/null &&
         cmake --build "$B$bits" -j"$(nproc)" >/dev/null; }; then
    log "STOP: build ($bits bits) failed"; exit 1
  fi
  if ctest --test-dir "$B$bits" > "$OUT/ctest$bits.log" 2>&1; then log "unit tests ($bits-bit build) passed"
  else log "WARNING: unit tests ($bits-bit build) FAILED"; fi
done

echo "case,exit_code,peak_rss_gb,seconds" > "$OUT/runs.csv"
run() {  # run one check; record exit code, peak memory and duration; never abort
  local name=$1; shift
  log "start $name"
  local t0=$SECONDS rc rss="NA"
  /usr/bin/time -f "%M" -o "$OUT/.rss" "$@" >> "$OUT/bench.log" 2>&1; rc=$?
  rss=$(tail -n 1 "$OUT/.rss" 2>/dev/null | awk '{printf "%.2f", $1 / 1048576}')
  echo "$name,$rc,$rss,$(( SECONDS - t0 ))" >> "$OUT/runs.csv"
  log "end   $name: exit $rc, peak $rss GB, $(( SECONDS - t0 )) s"
}

for bits in 4 5; do
  cases=$CASES4; [[ $bits == 5 ]] && cases=$CASES5
  for c in ${cases//,/ }; do
    run "verify_${c//:/_}" "$B$bits/verify_large" --zeta "$c" --sweep-gb 400 --samples 400 --out "$OUT/verify_large.csv"
  done
done
for c in ${KCASES//,/ }; do
  run "verify_kernel_${c//:/_}" "${B}4/verify_large" --kernel "$c" --samples 400 --out "$OUT/verify_large.csv"
done

rm -f "$OUT/.rss"
log "DONE"
