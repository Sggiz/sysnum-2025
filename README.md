# Project : Microprocessor (2025-26)

Project of the L3-S1 course "Systèmes Numériques".
Source code on [GitHub](https://github.com/Sggiz/sysnum_project)

## 1. The netlist simulator

#### Project execution

- Bash : `bash run <netlsist-file>` (no step limitor)
- Dune : `dune exec nlsim <netlist-file>` (no step limitor)
- Direct execution : build the project with `dune build` then run the
    executable :
    `_build/default/netlist_simulator.exe [-n <steps>] <netlist-file>`

#### Implementation of the simulator

My Programming language of choice is OCaml. I reused the resources given during
lab session 1 (lexer, parser, printer, graph module, tests, the scheduler I
coded during that session).

The input netlist is expected to be correct. Very little verification is done
by the netlist simulator ; some issues with the input would be found by the
netlist lexer/parser, or the scheduler (cycles).

Boolean operations are only applied to single bits, and are implemented in a
natural way on values of type VBit(_).

Operations on buses have to follow some implicit functions : slicing on a single
bit outputs a bit, and not a bit array. Generally, the simulator avoids the
manipulation single-bit arrays, to be consistent with boolean operations.

Simultation is done top-down, which is made possible by the scheduler's
preprocessing. Variable values are stored inside an environment
and are passed down to the next cycle
for register evaluation.

Regarding ROMs and RAMs, every such memory-type equation in the netlist is
linked by its ident to a suited array. I assumed that identifiers
cannot be defined multiple times in the netlist (what I include in the
"correctness" of the netlist); every instance of a ROM/RAM hence has its
own independent memory table.

#### Difficulties

One non-trivial implementation decision was the choice of data structures used
for the variable environments and memory management.
After having tried to manipulate
hash tables for environments, I decided to switch to the previously-defined
environments in `netlist_ast.ml` (`module Env`) as its immutable nature made
its "passing down" to the following cycle more natural. Hash tables remained
my choice for memory, as a mutable data structure seemed relevant for memory
implementation.

The behaviour of some netlist equations had to be interpreted, which wasn't
always obvious to me : The type of a binary operator's arguments, the
implicit conversions after some slices or before concatenation,
the addressing structure of memory (`addr_size` and `word_size`), and finally
the independence of memory between different instances of ROM/RAMs in the
netlist.

