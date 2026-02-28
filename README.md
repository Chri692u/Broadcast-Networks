# Modules
### Model
Definitions of process types for broadcast networks:
- Processs type definition
- The Wait-only restriction
- Planned: process types with registers

### Semantics
Definitions for the semantics of broadcast networks assuming reliable and unreliable communication. The semantics differ depending on the considered architectures:
- Cliques
- Arbitrary graphs

The semantics introduce a parameter for network size along with a "step" function which allows for simulation of the networks.

### Reachability
todo

# Compiling Dafny
Dafny is a language that compiles to different targets such as Java, C# and Python. Here is a non-exhaustive list of options:
- dafny build -t:java MyProgram.dfy // For Java
- dafny build -t:cs MyProgram.dfy // For C#
- dafny build -t:py MyProgram.dfy // For Python3
- dafny build -t:js MyProgram.dfy // For JavaScript
- dafny build -t:go MyProgram.dfy // For Golang
- dafny build -t:cpp MyProgram.dfy // For C++
- dafny build -t:rs MyProgram.dfy // For Rust

To build and run the code immediately, replace `build` with `run` in the command. See [here](https://dafny.org/latest/Installation) for the installation process.

# References
### [On Verification of Broadcast Protocols](https://archive.model.in.tum.de/um/bibdb/esparza/LICS99.pdf)
The main result of this paper is decidability of safety properties in broadcast networks, notably applying an algorithm for [General decidability theorems for infinite-state systems](https://ieeexplore.ieee.org/document/561359) for broadcast networks showing that reachability is decidable with very high complexity.

### [On the Complexity of Parameterized Reachability in Reconfigurable Broadcast Networks](https://www.irif.fr/~sangnier/publis/DSTZ-FSTTCS12-long.pdf)
This paper considers unreliable broadcast for arbitrary graphs and gives a PTime-complete algorithm to compute the set of reachable states, additionally it is also proven that placing restrictions on cardinality of states is PTime-complete for cardinalities [≥ 1,= 0] and PSpace complete for full cardinality constrains.

### [Safety Verification of Wait-Only Non-Blocking Broadcast Protocols](https://arxiv.org/abs/2403.18591)
Here it is shown that placing a restriction on broadcast protocols in clique topologies makes reachability and coverability much easier. The main result for broadcast networks with clique topologies is P-complete for reachability and PSpace-complete for coverability.