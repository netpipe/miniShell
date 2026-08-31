# sample2.sh
# Test if / while / for / functions

NAME="patched"
echo "Testing $NAME"

if [ "$NAME" = "patched" ]; then
    echo "if: string comparison works"
else
    echo "if: unexpected branch"
fi

always_true() {
    return 0
}

if always_true; then
    echo "if: function condition works"
fi

greet() {
    echo "function greet: hello $1"
    return 0
}

greet Alice
greet Bob

LOOP_FILE="/tmp/minishell-loop-$$.txt"
echo x > "$LOOP_FILE"

while [ -f "$LOOP_FILE" ]; do
    echo "while: loop file exists, removing it now"
    rm -f "$LOOP_FILE"
done

echo "while: loop finished"

for word in alpha beta gamma; do
    echo "for: $word"
done

for i in 1 2 3 4; do
    if [ "$i" = "3" ]; then
        continue
    fi

    echo "for flow control: i=$i"

    if [ "$i" = "4" ]; then
        break
    fi
done

echo "sample done"