#!/usr/bin/env bash
# Kill any Lean process above 64 GB of resident memory, so one runaway
# elaboration cannot take the pod down. Virtual-memory limits do not work here:
# Lean reserves about ten times what it uses, which starves it of threads.
while sleep 10; do
    ps -eo pid=,rss=,comm= | awk '$3 == "lean" && $2 > 64 * 1024 * 1024 { print $1, $2 }' |
    while read -r pid rss; do
        echo "$(date -u) killed lean pid $pid at $((rss / 1048576)) GB" >> "$HOME/pf/watchdog.log"
        kill -9 "$pid"
    done
done
