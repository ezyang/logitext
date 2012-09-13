#!/bin/bash
# Continuous build script
# XXX handle interrupts gracefully
NAME=logitext
if [ -f config ]
then
    . config
fi
pkill $NAME.exe
while true
do
    reset
    (
        ghc -Wall -Werror --make -c ClassicalFOLFFI.hs && \
        ghc -Wall -Werror --make -c haskell.c && \
        urweb $URWEB_FLAGS $NAME && \
        ./$NAME.exe
        #(./$NAME.exe &) && \
        #sleep 1 && \
        #(curl "http://localhost:8080/main" &> /dev/null)
    ) &
    PID=$!
    inotifywait -e modify $(git ls-files '*.ur' '*.urp' '*.urs' '*.hs' '*.c' '*.h') 2> /dev/null
    kill $PID
    pkill $NAME.exe
done
