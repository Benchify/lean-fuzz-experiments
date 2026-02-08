#!/bin/bash
# Parallel fuzzer runner - spawns multiple fuzzer instances
#
# Usage: ./run_parallel.sh [num_jobs] [depth]
# Example: ./run_parallel.sh 4 10
#   Runs 4 parallel fuzzer instances with depth 10

JOBS=${1:-4}
DEPTH=${2:-15}

echo "[*] Starting $JOBS parallel fuzzer instances with depth $DEPTH"
echo "[*] Press Ctrl+C to stop all instances"

# Trap Ctrl+C to kill all background jobs
trap 'echo "Stopping all fuzzers..."; kill $(jobs -p); exit' INT

cd generator

# Start fuzzer instances in background
for i in $(seq 1 $JOBS); do
    echo "[*] Starting fuzzer instance $i/$JOBS"
    RUST_LOG=warn cargo +nightly run --release --bin main -- --depth $DEPTH &
    sleep 0.5  # Stagger starts slightly
done

# Wait for all background jobs
wait

echo "[*] All fuzzers completed"
