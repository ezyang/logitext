#!/bin/bash
# Continuous build script
while true
do
    pkill logitext.exe
    reset
    ghc -c ClassicalFOLFFI.hs haskell.c
    urweb logitext
    ./logitext.exe &
    inotifywait -e modify $(git ls-files)
done
