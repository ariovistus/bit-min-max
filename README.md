This project contains algorithms to find the min or max of bitwise AND, OR, and XOR given two ranges of possible values. 

There's also a paper I never finished (or made readable) that explains the derivation of these algorithms.

Usage is pretty simple:

import bitall;

void main() {
    byte min = minOr!byte(1, 2, 1, 2);
    byte max = maxOr!byte(1, 2, 1, 2);
    assert(min == 1);
    assert(max == 3);
}
