# Explainable Monitoring of Regular Expressions

This is a repository forked from **WhyMon** and is extended as part of Rosa Haslund Meyer's bachelor thesis (2025) in Explainable Monitoring of Regular Expressions, at the University of Copenhagen, Department of Computer Science with Dmitriy Traytel as superviser and Leonardo Lima as co-supervisor. 

Note, that the below describtion will not differ much from that of the original WhyMon repository. 

# WhyMon: explanations as verdicts

The extension of **WhyMon** is a runtime monitoring tool that produces explanations as verdicts of metric first-order dynamic logic (MFODL) formulas.

## Getting Started

To execute the project locally, follow the instructions below.

### Prerequisites

**WhyMon** is written in OCaml and requires a recent version of the OCaml compiler
(>= 4.11). We recommend installing OCaml's package manager
[opam](https://opam.ocaml.org/doc/Install.html), which includes OCaml's compiler.

For instance, you can create an OCaml `5.1.0` switch and initialize the environment
variables of your terminal by running

```shell
$ opam switch create 5.1.0
$ eval $(opam config env)
```

To install **WhyMon**'s dependencies, run

```shell
$ opam install dune core_kernel base zarith menhir js_of_ocaml js_of_ocaml-ppx zarith_stubs_js
```

At this point, you are able to locally execute **WhyMon**'s command line
interface (CLI).

However, to locally execute **WhyMon**'s graphical user interface (GUI), you
also need [Node.js](https://nodejs.org/en/download/package-manager) and an
[Ace editor's fork](https://github.com/leonardolima/ace-mfotl) that includes
syntax highlighting for **WhyMon**'s inputs.

Specifically, run

```shell
$ npm install
```

from the `vis` folder to install the GUI's dependencies. Furthermore,
assuming that both `whymon` and `ace-mfotl` are located in the same folder, run

```
$ npm install
$ ./build_copy.sh
```

from the `ace-mfotl` folder.

### Running (CLI)

From **WhyMon**'s root folder, you can compile the code with

```
$ dune build
```

This generates the `bin/whymon.exe` executable. Moreover, running

```
$ ./bin/whymon.exe
```

presents **WhyMon**'s CLI usage statement.

To experiment with **WhyMon**'s CLI interface, you can execute the
`three_attempts_copy` example that detects access behavior to some system. In particular, the policy 
`examples/paper-tool/three_attempts_copy.mfotl` (note that the formula is an MFODL formula)
specifies a pattern where a single user attempts an action (e.g., authentication or access) tto a system and is 
then followed by some another event. This formula could for example be used to detect cases where a user initiates 
an authentication attempt, followed by some other action, which could indicate suspicious behavior such as multiple 
login attempts, location changes, or additional security checks.

You can run this example with

```
$ ./bin/whymon.exe -sig examples/paper-tool/three_attempts.sig \
                   -formula examples/paper-tool/three_attempts_copy.mfotl \
                   -log examples/paper-tool/three_attempts.log
```

**WhyMon** inputs the MFODL formula `three_attempts_copy.mfotl`, the trace
`three_attempts.log`, and the signature file `three_attempts.sig` that
specifies the events (and their data parameter types) in the trace.

**WhyMon** outputs explanations in the form of partitioned decision trees
(PDTs) [[Lima et al., TACAS'24]][2].

We distinguish time-points (indices into the trace) and time-stamps,
which are attached to the time-points and denote real time (e.g., a Unix
timestamp).

For instance, in this example, at time-point 1 (with time-stamp 7) the
explanation is the following

```
7:1
Explanation: 

    ❮

    c1 ∈ Complement of {NO}

        ❮

        u ∈ Complement of {}

            ❮

            VPrex{1}
                [ VConcat{0, 1}
                    [ true
                    VTest{0, 0}
                        VPred(0, att, u, c1)
                    ; true
                    VTestNeq{0, 1} ]
                ; VConcat{1, 1}
                    [false
                    VWild{1, 1}] ]
            ❯
        ❯


    c1 ∈ {NO}

        ❮

        u ∈ Complement of {6}

            ❮

            VPrex{1}
                [ VConcat{0, 1}
                    [ true
                    VTest{0, 0}
                        VPred(0, att, u, c1)
                    ; true
                    VTestNeq{0, 1} ]
                ; VConcat{1, 1}
                    [false
                    VWild{1, 1}] ]
            ❯

        u ∈ {6}

            ❮

            SPrex{1}
                SConcat{0, 1}
                    STest{0, 0}
                        SPred(0, att, u, c1)
                    SWild{0, 1}
            ❯

        ❯


    ❯
```

Here, `Complement of {}` corresponds to the infinite domain $\mathbb{D}$. Hence,
`x ∈ Complement of {}` denotes that the variable $x$ can be assigned to any
value of the domain.

For instance, considering the assignment `c1 ∈ {NO}`,
`u ∈ {6}`, the associated proof tree corresponds to a satisfication
of the SPrex construc for the variable $u ∈ {6}$ at time-point 1
(`SPrex{1}`).

You can also run this example with the option `-mode verified`:

```
$ ./bin/whymon.exe -mode verified \
                   -sig examples/paper-tool/three_attempts.sig \
                   -formula examples/paper-tool/three_attempts.mfotl \
                   -log examples/paper-tool/three_attempts.log
```

from **WhyMon**'s root folder. To filter the explanation checker output,
we send **WhyMon**'s CLI output through a pipe (`|`) to **grep**. For instance,

```
$ ./bin/whymon.exe -mode verified \
                   -sig examples/paper-tool/three_attempts.sig \
                   -formula examples/paper-tool/three_attempts.mfotl \
                   -log examples/paper-tool/three_attempts.log | grep "Checker output:"
```

yields

```
Checker output: true
Checker output: true
Checker output: true
Checker output: true
Checker output: true
Checker output: true
```

Indicating the validity of all explanations produced by **WhyMon**'s monitoring algorithm
(one for each of the 6 time-points included in the trace).

For more details on the proof trees and the proof system rules, you can check
[[Lima et al., TACAS'24]][2].

### Running (GUI)

From the `vis` folder, you can start the GUI with

```
$ npm start
```

At this point, a non-deterministic issue regarding a path computation might arise.
To fix this issue, run

```
$ ./tools/fix_path.py
```

from **WhyMon**'s root folder.

Now, you can select, run and interactively explore the included examples using
**WhyMon**'s GUI.

Clicking on the `?` button (in the main page) presents **WhyMon**'s syntax.
In addition, the GUI's usage has been described in the GUI's
[Quickstart](http://localhost:3000/whymon/quickstart) page, [[Lima et al., TACAS'24]][2] and [[Lima et al., ATVA'24]][4].

### Checker

This step requires [Isabelle2024](https://isabelle.in.tum.de/) and depends on the
corresponding [Archive of Formal Proofs (AFP) version](https://www.isa-afp.org/download/).

The file `src/checker.ml` corresponds to the code extracted from
our checker formalized in the proof assistant Isabelle. This formalization has been
published in the AFP [[Herasimau et al., AFP]][3]. Alternatively, you can extract this code
from the current repository on your local machine by running

```
$ isabelle build -vd thys -eD code
```

from inside the `formalization` folder. This generates the file
`formalization/code/checker.ocaml`, which is identical to the already included file
`src/checker.ml`.

[1]: <https://doi.org/10.1007/978-3-031-30820-8_28> (Explainable Online Monitoring of Metric Temporal Logic, TACAS'23)
[2]: <https://doi.org/10.1007/978-3-031-57246-3_16> (Explainable Online Monitoring of Metric First-Order Temporal Logic, TACAS'24)
[3]: <https://www.isa-afp.org/entries/MFOTL_Checker.html> (A Verified Proof Checker for Metric First-Order Temporal Logic, Archive of Formal Proofs)
[4]: <https://traytel.bitbucket.io/papers/atva24-whymon-tool/whymon-tool.pdf> (WhyMon: A Runtime Monitoring Tool with Explanations as Verdicts, to appear at ATVA'24)

### Syntax

#### Metric First-Order Dynamic Logic
```
{PRED} ::= string

{VAR} ::= string

{VARS} ::=   {VAR}
           | {VAR}, {VARS}

{CONST} ::= quoted string

{I}  ::= [{NAT}, {UPPERBOUND}]

{UPPERBOUND} ::=   {NAT}
                 | INFINITY   (∞)

{f} ::=   {PRED}({VARS})
        | true                  (⊤)
        | false                 (⊥)
        | {VAR} EQCONST {CONST} (=)
        | NOT {f}               (¬)
        | {f} AND {f}           (∧)
        | {f} OR  {f}           (∨)
        | {f} IMPLIES {f}       (→)
        | {f} IFF {f}           (↔)
        | EXISTS {VAR}. {f}     (∃)
        | FORALL {VAR}. {f}     {∀}
        | PREV{I} {f}           (●)
        | NEXT{I} {f}           (○)
        | ONCE{I} {f}           (⧫)
        | EVENTUALLY{I} {f}     (◊)
        | HISTORICALLY{I} {f}   (■)
        | ALWAYS{I} {f}         (□)
        | {f} SINCE{I} {f}      (S)
        | {f} UNTIL{I} {f}      (U)
        | {f} TRIGGER{I} {f}    (T)
        | {f} RELEASE{I} {f}    (R)
        | FREX{I} {f}           (▷)
        | PREX{I} {f}           (◁)
        | PLUS                  (PLUS)
        | CONCAT                (CONCAT)
        | ?                     (?)
        | *                     (*)
```

Note that this tool also supports the equivalent Unicode characters (on the right).

#### Signature
```
{TYPE} ::= string | int

{VARTYPES} ::=   {VAR}:{TYPE}
               | {VAR}:{TYPE}, {VARTYPES}

{SIG} ::=   {PRED}({VARTYPES})
          | {PRED}({VARTYPES}) \n {SIG}
```

#### Trace
```
{VALUES} ::=   string
             | string, {VALUES}

{TRACE} :=   @{NAT} {PREDICATE}(VALUES)*
           | @{NAT} {PREDICATE}()* \n {TRACE}
```

where `0 <= {NAT} <= 2147483647`.

## License

The original WhyMon project is licensed under the GNU Lesser GPL-3.0 license - see [LICENSE](LICENSE) for details.
