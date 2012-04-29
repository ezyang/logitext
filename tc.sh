#!/bin/bash
# Continuous type check script
while true
do
    reset
    (urweb -tc logitext && echo "Type check OK") &
    PID=$!
    inotifywait -e modify $(git ls-files) 2> /dev/null
    kill $PID
done
