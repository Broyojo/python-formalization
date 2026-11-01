cd lean && lake build 2>&1 | grep -vE "^info|Building|Compiling|Downloading|trace|^⚠|^✔|warning: .*linter|declaration uses|^  |Hint:|^$" | grep -iE "error|sorry|Build completed|✖|failed" | head -40
