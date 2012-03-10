#!/bin/sh
# Continuous build script
while true
do
    reset
    urweb logitext
    ./logitext.exe &
    inotifywait -e modify *.ur *.urs *.urp *.h
    pkill logitext.exe
done
