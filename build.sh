#!/bin/bash
# Continuous build script
# XXX handle interrupts gracefully
if [ -f config ]
then
    . config
fi
pkill logitext.exe
while true
do
    reset
    (
        ghc -Wall -Werror --make -c ClassicalFOLFFI.hs && \
        ghc -Wall -Werror --make -c haskell.c && \
        urweb $URWEB_FLAGS logitext && \
        ./logitext.exe
        #(./logitext.exe &) && \
        #sleep 1 && \
        #(curl "http://localhost:8080/main" &> /dev/null)
    ) &
    PID=$!
    inotifywait -e modify $(git ls-files) 2> /dev/null
    kill $PID
    pkill logitext.exe
done
