# Bash With Floats

A fork of bash with support for floating-point expansion and variables.

## Modifications

- Added **{{...}}** (float-expansion) and **${{...}}** (float-substitution)
- Added the "-d" ("double-precision floating-point") option to the *declare*/*typeset* builtin, and corresponding behavior

## Usage

Run "**./configure && make && ./bash**" to configure, compile, and run the modified version of bash.

The **{{...}}** construct works almost identically to **((...))** (arithmetic expansion), except that floating-points are used instead of integers.

The **FLOAT_DIGITS** variable can be changed to adjust the number of digits printed after the decimal (it defaults to 6).

**declare -d** is analagous to **declare -i** except for floating-point numbers instead of integers.
When a variable declared as float is assigned to, the right-hand-side of variable assignments is expanded using float-expansion, and the += operator does float-addition instead of string concatenation.