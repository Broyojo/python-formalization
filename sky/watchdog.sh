#!/usr/bin/env bash
# The pod's only SkyPilot job. SkyPilot does not count work done over ssh as
# activity, so while this runs the pod is not idle; it exits once no Lean
# process has run for two hours, and autostop then tears the pod down.
# It also kills any Lean or pydiff process above 64 GB of resident memory, so one
# runaway elaboration or difftest case cannot take the pod down. Virtual-memory limits do not work here:
# Lean reserves about ten times what it uses, which starves it of threads.
idle=0
while [ "$idle" -lt 720 ]; do
    sleep 10
    if pgrep -x lean >/dev/null; then idle=0; else idle=$((idle + 1)); fi
    ps -eo pid=,rss=,comm= | awk '($3 == "lean" || $3 == "pydiff") && $2 > 64 * 1024 * 1024 { print $1, $2 }' |
    while read -r pid rss; do
        echo "$(date -u) killed pid $pid at $((rss / 1048576)) GB" >> "$HOME/pf/watchdog.log"
        kill -9 "$pid"
    done
done
