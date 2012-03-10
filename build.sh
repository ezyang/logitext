#!/bin/bash
# Continuous build script
while true
do
    pkill logitext.exe
    reset
    gcc -c coq.c
    urweb logitext
    ./logitext.exe &
    inotifywait -e modify $(git ls-files)
done
