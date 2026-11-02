#!/usr/bin/env bash
# Re-run of the phase-5 verification campaign (the first run was lost when the
# instance was destroyed).  Same cases as before, split over four jobs, two per
# socket, since nothing here is timed.  Run from the repository root.
set -euo pipefail
# the case lists of the first run
OLD1="9:6:4,8:6:4,7:6:4,16:5:3,4:7:5,13:5:3,11:5:4,2:9:7,5:6:4,9:5:3,3:7:5,8:5:3,4:6:4,7:5:4,2:8:6,16:4:3,3:6:5,13:4:3,5:5:3,11:4:3,2:7:5,4:5:4,9:4:3,8:4:3,7:4:3,3:5:4,2:6:5,5:4:3,16:3:2,4:4:3,13:3:2,2:5:4,11:3:2,3:4:3,9:3:2,8:3:2,7:3:2,2:4:3"
OLD0="5:7:4,2:10:8,3:8:6"
OLD5="32:3:2,32:4:3,32:5:3"
OLDK="8:6:3,3:8:4,2:10:5,5:6:3,4:6:3,2:8:4,3:6:3,2:6:3,2:4:2,3:4:2,4:4:2,5:4:2"

A4="9:6:4,7:6:4,4:7:5,2:9:7,9:5:3,3:7:5,8:5:3,4:6:4,7:5:4,2:8:6"
B4="8:6:4,16:5:3,13:5:3,11:5:4,5:6:4"; B5="$OLD5"
C4="$OLD0"
D4="16:4:3,3:6:5,13:4:3,5:5:3,11:4:3,2:7:5,4:5:4,9:4:3,8:4:3,7:4:3,3:5:4,2:6:5,5:4:3,16:3:2,4:4:3,13:3:2,2:5:4,11:3:2,3:4:3,9:3:2,8:3:2,7:3:2,2:4:3"; DK="$OLDK"

sorted() { tr ',' '\n' | sort; }
diff <(echo "$OLD1,$OLD0" | sorted) <(echo "$A4,$B4,$C4,$D4" | sorted) || { echo "4-bit cases differ from the first run"; exit 1; }
echo "case lists match the first run: $(echo "$A4,$B4,$C4,$D4" | tr ',' '\n' | wc -l) 4-bit, 3 5-bit, $(echo "$DK" | tr ',' '\n' | wc -l) kernel"

go() {  # name node cases4 cases5 kcases
  CASES4=$3 CASES5=$4 KCASES=$5 OUT=results_phase5_$1 BDIR=build_$1_ OMP_NUM_THREADS=14 \
    setsid nohup numactl --cpunodebind=$2 bash scripts/run_phase5.sh < /dev/null > run_phase5_$1.log 2>&1 &
  echo "started $1 on node $2 (pid $!)"
}
go a 1 "$A4" "" ""
go b 1 "$B4" "$B5" ""
go c 0 "$C4" "" ""
go d 0 "$D4" "" "$DK"
