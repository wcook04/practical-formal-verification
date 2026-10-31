# Plectis

**Python programs and examples for checking research and software results.**

Plectis contains small programs that decide which results to recalculate after
a change, check an AI assistant's claims about completed work, compare forecasts
and check that documents agree with their source files. Some of the calculations
have mathematical proofs; others are tested against example inputs.

Start below: change a scoring rule and see which previous results can be reused.
You need Python and Git, but no AI account. This is a research prototype.

[Run the example](#formally-checked-workflow-operations) ·
[Open the component map](https://wcook04.github.io/practical-formal-verification/explorer/) ·
[Documentation](docs/README.md) ·
[Will Cook’s projects](https://wcook04.github.io/)

<a id="formally-checked-workflow-operations"></a>

### First example: change a scoring rule

A workflow is a sequence of tasks, such as collecting data, scoring it and
writing a report. This example asks: **“I changed the scoring rule. Which
results can I keep, and what must run again?”** With Git and Python 3.11 or
newer, run:

```bash
git clone --depth 1 https://github.com/wcook04/practical-formal-verification
cd practical-formal-verification
PYTHONPATH=src python3 examples/operations/evaluation.py --format text
```

The program prints `8 reused, 3 rerun, 1 blocked`. It keeps eight earlier
results, runs the three affected tasks again and blocks an action that cannot
safely be repeated. It also rejects an old worker trying to overwrite a newer
result. The example runs locally in a temporary directory, without calling an
AI model. The [walkthrough](docs/guides/verification-study.md) explains the
inputs, decisions and output.

Some calculations in these programs have **formal proofs**: mathematical
arguments checked by a tool called Dafny against precise specifications and
stated assumptions. A proof covers the specified calculation; it does not establish
that every part of the Python program, its database or an outside service is
correct.

You can also use the following functions in your own Python programs:

| Python module | What it does | Code and proof |
|---|---|---|
| [`plectis.repair`](docs/guides/repair.md) | Decides which results can be reused after a declared change. | [Task-dependency proof](formal/repair/Repair.dfy) and [generated Python](src/plectis/repair/_generated/Repair.py). |
| [`plectis.compatibility`](docs/guides/compatibility.md) | Checks whether a replacement preserves allowed actions and outputs in the supplied descriptions of program behaviour. | [Proof](formal/compatibility/Compatibility.dfy) and [generated Python](src/plectis/compatibility/_generated/Compatibility.py). |
| [`plectis.views`](docs/guides/public-views.md) | Builds a public-only report-writing program from supplied report instructions, preserving the public output under the stated rules. | [Proof](formal/views/Release.dfy) and [generated Python](src/plectis/views/_generated/Release.py). |
| [`plectis.publish`](docs/guides/publish.md) | Checks whether a worker can still save its result as the current one. | [Tested database code](src/plectis/publish.py); no formal implementation proof. |

Dafny translates the proved calculations into Python. The `repair`,
`compatibility` and `views` modules call that generated code. The proofs cover the supplied task dependencies, descriptions
of program behaviour and report-writing rules. They do not cover the Python
code that prepares inputs, SQLite storage or external services. Each module
can be imported separately; [copying and installation instructions](examples/operations/README.md)
explain how.

An ordinary cache makes the same reuse decisions in this example. Whether the
proved version is more useful in practice still needs evaluation.

<details>
<summary>Recheck the formal proofs</summary>

With **Dafny 4.11.0**, run:

```bash
make verify-operations DAFNY=/path/to/dafny
```

This checks the three calculations above and a fourth that checks saved
component runs. It regenerates their Python and compares the files byte for
byte. Deliberately broken versions must fail the checks. `make check` compares
the saved file fingerprints without running Dafny. Read the
[assumptions and trusted tools](formal/README.md) before adapting a proved
calculation to another use.

Twelve other small calculations have
[their own specifications and proofs](formal/components/README.md).

</details>

### Try the repository tour

To list the files in the repository and get a suggested next step, run:

```bash
PYTHONPATH=src python3 -m plectis tour --format text .
```

The tour lists project files, suggests a task and saves an inventory and a
simulated task record under `.microcosm/`, a local folder ignored by Git. It does not run your tests or change your source.
[How it works](#how-it-works) explains where those files go.

## Can I use it today?

You can run the examples and use the four Python modules above. Start with
the [workflow example](docs/guides/verification-study.md) or
[quickstart](QUICKSTART.md). Before using a program on your own project, read
its required inputs, tools and stated limits.

The catalogue contains 88 separate components. A **component** is a named
program or small group of programs with example inputs and instructions for
checking its result. Some need tools such as Lean, which checks mathematical
proofs, or Swift, a programming language and compiler. The catalogue explains
each component’s requirements; it is not a ready-made system for automating
all of a research project.

The [overview](docs/overview.md#the-public-workflow) follows one command from
input to output. The larger private research system is separate from this
repository.

## Checking a component result

Running a component again on its example inputs is called a **replay**.
It saves a **receipt**, a record of what ran, the inputs it used and the result
it returned. A separate checker compares the run with its saved record and the
component’s requirements. It rejects missing or duplicate results, changed
source or inputs, altered saved output and missing required execution evidence.

For example, run this from the repository root without installing the package:

```bash
PYTHONPATH=src python3 -m plectis component-replay pattern_binding_contract --root .
```

The result covers that component only. Its new files go under `.microcosm/`,
a local results directory excluded from Git. Missing inputs or tools are
reported as unavailable rather than passed. The
[replay guide](docs/maintainers/validation.md#fresh-component-replays) explains
how to read the result.

<details>
<summary>Check all components and inspect the proof boundary</summary>

```bash
make component-replays
```

This runs the current catalogue and writes results under
`.microcosm/component-replays/`. It needs the components’ required tools,
including Lean, its build tool Lake, and Swift. The
[study](docs/guides/verification-study.md#checking-the-component-replay-itself)
shows the deliberately incorrect records used to test the replay checker.

The [Dafny proof](formal/replay/README.md) requires exactly one matching result
for every selected component. It compares the captured source and input
identities, rules about what the result may claim, returned result, public
output sent to the receipt writer and saved receipt. The replay command calls
the Python generated from that proved calculation.

The checker records which source files and inputs were used, then compares the
produced result with the saved receipt. The proof covers that comparison.
Python code still collects the files and prepares the comparison inputs; that
code and the external tools it uses remain outside the proof. Repeating an
example successfully does not prove that its program is correct for all inputs.
The [implementation guide](docs/maintainers/architecture.md#single-component-replay)
and [component proof index](formal/components/README.md) give the exact coverage.

</details>

## Why this exists

Will Cook uses AI to research mathematics and build software. These examples
explore ways to check the resulting code and records so another person can
inspect what happened. The [project overview](docs/overview.md) explains the
larger effort; the [mathematics repository](https://github.com/wcook04/plectis-erdos)
contains the papers and proofs.

<a id="choose-a-route"></a>

## Choose a starting point

| You want to… | Start here |
|---|---|
| Find out what to rerun after a workflow change | [Run the verification study](docs/guides/verification-study.md) and [choose an operation](examples/operations/README.md) |
| Understand the project | [Why these tools belong together](docs/overview.md) |
| Run something locally | [Quickstart](QUICKSTART.md) |
| Follow a complete example | [Worked guides](docs/guides/README.md) |
| Find a tool in your field | [Component map](ORGANS.md) |
| Work on the code | [Contributing](CONTRIBUTING.md) and [implementation map](docs/maintainers/architecture.md#implementation-map) |
| Read the mathematics | [Companion reader's guide](https://github.com/wcook04/plectis-erdos/blob/main/docs/READING_GUIDE.md) |

## See it work

A separate [report example](docs/guides/public-views.md) changes instructions
for a report containing public and private information. It produces a public-only
version and checks that a private condition cannot decide whether a public line
appears. A separately written public-only program produces the same output;
whether maintaining the proved version is more useful still needs evaluation. Run it with:

```bash
PYTHONPATH=src python3 examples/operations/public_views_recipe_change.py
```

An AI says: “I committed the fix and the tests passed.” The
[completion-checking guide](docs/guides/checking-agent-completion.md) shows how
one component checks those claims using a sample Git repository and actual
pytest runs. It verifies three supplied claims and rejects four deliberately
incorrect ones. You can follow the result back to the code that checked it.

Two more [worked guides](docs/guides/README.md) show different uses:

- [Change a prompt-injection example](docs/guides/prompt-injection.md)
  and see a checker reject an inconsistent permission in saved records.
- [Prepare a research question](docs/guides/hypothesis-handoffs.md) with a
  tentative answer, alternatives and proposed observations for an expert.

Try the second example from the clone, without installing anything:

```bash
PYTHONPATH=src python3 -m plectis hypothesis-handoff \
  --input examples/hypothesis_handoff/independent_evaluation.json --format text
```

It validates the supplied file and prints the question and proposed
investigation. It does not answer the question, contact an expert or call a
model. Each guide explains what its example tests and what remains untested.

## What is in the toolkit?

The **88 components** are grouped into seven areas. Each has its own
instructions and stated limits. Some run a computation or an external tool; others compare supplied
records against rules. An entry in the catalogue is not a promise that every
example can run in every environment: its page lists required tools and source
files, and the runner reports unavailable requirements.

| Area | Try it for… |
|---|---|
| [Entry and orientation](ORGANS.md#entry--reveal) | Checking that a suggested first step names an available command and result file. |
| [Architecture and navigation](ORGANS.md#architecture--navigation) | Comparing a selection of files and components with an expected selection. |
| [Mathematics and proof](ORGANS.md#formal-math--proof) | Trying proof steps on supplied theorems and asking Lean to check them. |
| [Agent reliability and safety](ORGANS.md#agent-reliability--safety-replays) | Checking saved examples of attempts to mislead an AI assistant, conflicting memories or unsupported claims of completed work. |
| [Research and forecasting](ORGANS.md#research--science-replays) | Comparing forecast errors on synthetic data. |
| [Source and generated files](ORGANS.md#import-projection--drift) | Comparing file contents and checking that expected output files exist. |
| [Work and continuity](ORGANS.md#work-landing--continuity) | Checking that a work record names its changes, validation results and commits. |

<a href="https://wcook04.github.io/practical-formal-verification/explorer/">
  <img src="assets/system-map-dark.png" alt="Practical Formal Verification component explorer: proof dials at the centre and on component stems, with rings of recorded checks and the rules each component cites." width="100%">
</a>

[**Explore the component map →**](https://wcook04.github.io/practical-formal-verification/explorer/)
<br>
<sub>Select a component, proof or rule to inspect its source, recorded checks and limits. The map does not execute components or recheck proofs.</sub>

Browse the [component catalogue](https://wcook04.github.io/practical-formal-verification/explorer/catalogue.html)
and [coverage table](https://wcook04.github.io/practical-formal-verification/explorer/coverage.html).
The [project home](https://wcook04.github.io/) links the videos and related projects;
the [agent navigation guide](https://wcook04.github.io/practical-formal-verification/llms.txt)
provides text indexes and source links. For mathematics, follow the separate
[Plectis Mathematics website](https://wcook04.github.io/practical-formal-verification/map/),
[mathematics map](https://wcook04.github.io/practical-formal-verification/maths/universe.html)
or [Erdős reader’s guide](https://github.com/wcook04/plectis-erdos/blob/main/docs/READING_GUIDE.md).

To search component descriptions from the terminal:

```bash
PYTHONPATH=src python3 -m plectis comprehend --slice mechanism --format text
PYTHONPATH=src python3 -m plectis comprehend --first-action "prompt injection" --format text
```

The search uses phrase and word matching to suggest a command and relevant files.
It neither calls an AI model nor executes the suggested command.

## How it works

Most components run independently. They share the code that reads commands,
common file formats and a catalogue listing each component’s code, inputs,
checks and saved results. The documentation and maps are built from those same
records.
The connections between components are recorded where they exist; the seven
areas are a browsing aid, not seven stages that every run executes.

To understand a component, open its example input, the source function that
processes it and the output it produces. Compare that output with the test or
expected result. Then change an input in a disposable copy and check whether
the result changes as expected. The [worked guide](docs/guides/prompt-injection.md)
follows this path through one component.

The project tour is a separate orientation command. It mostly classifies
filenames and paths, with limited inspection of Python entry points. It
writes a file inventory, suggested tasks and a simulated task record under
`.microcosm/`, an ignored directory retained from the project's former name.
To see the tour's structured output:

```bash
PYTHONPATH=src python3 -m plectis tour --card .
```

[Architecture](ARCHITECTURE.md) maps the implementation. The
[maintainer guides](docs/maintainers/README.md) explain command dispatch,
data ownership and how to regenerate the maps.

## Explore with a coding agent

You can ask an AI coding assistant to find an example, explain its inputs,
run it and show you the result and checking code. The
[agent quickstart](QUICKSTART.md#use-your-own-coding-agent) explains how;
[AGENTS.md](AGENTS.md) contains instructions for editing this repository.
The examples need no model API key. Your assistant has its own account requirements.

## Install

The basic commands run from a clone with **Python 3.11 or newer**, without
third-party runtime dependencies. The shell examples above work on macOS,
Linux and WSL. In Windows PowerShell, first set `$env:PYTHONPATH = 'src'`,
then use `python -m plectis` in place of `PYTHONPATH=src python3 -m plectis`.
Individual examples may require Git, pytest, Lean or other tools; follow the
selected example's instructions.

To install the shorter `plectis` command on macOS or Linux:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install .
.venv/bin/plectis tour --format text .
```

Use the virtual environment if your system Python reports
[`externally-managed-environment`](https://peps.python.org/pep-0668/).
For development dependencies, Windows
installation commands and other options, see [Quickstart](QUICKSTART.md),
[Contributing](CONTRIBUTING.md) and [troubleshooting](docs/README.md#troubleshooting).
The older `microcosm` command remains an alias.

<a id="build-a-frontend-against-the-component-backend"></a>

## Explore the components locally

The [component explorer](frontend/README.md) shows the sixteen computations
proved with Dafny, the components that call them and the recorded checks for
each component. Select an item to read its description, source and limits.
With Python 3.11+, run from this clone:

```sh
python3 frontend/serve.py --start-backend
```

Open <http://127.0.0.1:8767/>. `make explorer` starts the same servers. No
installation or model API key is needed. The explorer reads a validated
snapshot; it does not run components or recheck proofs. For a hosted copy,
[open the public explorer](https://wcook04.github.io/practical-formal-verification/explorer/).

### Build another client

The local server also provides an API: addresses another program can request
to read component descriptions and saved results or search the catalogue.
Follow the [API reference](docs/reference/component-http-api.md) and
[implementation guide](docs/guides/frontend-implementation.md). The server
reads saved results; it does not run components or recheck proofs.

## Repository layout

Each component has records naming its description, source files, commands and
what its checks establish. [`component_descriptions.py`](src/microcosm_core/component_descriptions.py)
reads the descriptions; records under `core/` and `atlas/` supply the structure
and claims. The [architecture guide](docs/maintainers/architecture.md) explains
which record to edit.

For the verified operations, start with `formal/`, `src/plectis/` and
`examples/operations/`. The broader component catalogue, generated indexes and
recorded experiments remain available separately; they are not prerequisites
for using these APIs.

```text
practical-formal-verification/
├── formal/               Proofs and deliberately broken examples used to test them
├── src/
│   ├── plectis/           Python functions and command-line tools
│   └── microcosm_core/    Python implementation; components in organs/
├── frontend/             Browser explorer, local server and static exporter
├── docs/                 Guides, reference, maintainer notes and paper guide
├── examples/             Runnable examples and the source files they use
├── fixtures/             Prepared inputs and expected results
├── tests/                Executable checks
├── core/                 Component registry and configuration
├── atlas/                Generated maps and indexes
├── standards/            Requirements checked by the tools
├── skills/               Procedures for agents
├── paper_modules/        Component explanations
├── paper/                Toolkit paper source
├── receipts/             Recorded example results
├── assets/               README and social preview images
└── scripts/
    ├── build/            Documentation and map generators
    ├── check/            Checks for source files, generated output and stated limits
    ├── release/          Packaging and release verification
    ├── inspect/          Compact inspection cards
    └── papers/           Publication corpus tools
```

Start with the [examples](examples/README.md); use the
[fixtures](fixtures/README.md) and [recorded results](receipts/README.md) to
understand their checks. Your own runs go in the ignored `.microcosm/` directory.
The [paper guide](docs/papers/README.md) distinguishes the toolkit paper's
[source](paper/README.md) from the main research papers.

The root `ORGANS.md`, `ARCHITECTURE.md` and `AGENT_ROUTES.md` are generated
indexes. `AXIOMS.md`, `PRINCIPLES.md` and `ANTI_PRINCIPLES.md` contain the
[doctrine shown in the map](docs/reference/README.md#the-doctrine-in-the-map).
`Makefile` and `.github/workflows/` run the checks. The
[maintainer architecture guide](docs/maintainers/architecture.md) identifies
which files to edit and which builders to run. The [script guide](scripts/README.md)
explains each maintenance role; `make check` enforces their placement in Git
and CI.

Exported examples include copies of the code they use in `source_modules/`,
with records identifying the originals. The installed examples need those copies.
Old results remain as records of their original runs; rerunning an example
writes a new result. See the [documentation index](docs/README.md) for guides
and the [terminology guide](docs/reference/terminology.md) for older source names.

<a id="how-the-result-stays-honest"></a>

## What a passing result means

A pass is about a particular input and check. The component records classify
the result: a computation run now, a replay of supplied data, or a comparison
of files. That is why the source, test and stated limits are published together.

<details>
<summary>Limits by kind of example</summary>

- **Formal proof:** Lean can check the supplied formal statement and proof.
  A successful toolkit example does not prove an unrelated theorem.
- **Agent safety:** a replay does not establish that a deployed agent is safe.
  Its prepared cases cover specific checks, not every possible attack.
- **Research and forecasting:** synthetic examples do not establish scientific
  expertise, investment returns or a forecasting track record. This is not
  professional advice or investment advice.
- **Generated files:** a match establishes agreement for the specified files.
  You do not gain permission to publish private material by comparing them.
- **Recording and resuming work:** you do not gain permission to edit someone
  else's source files or publish a release by recording a task as complete.

</details>

This is a research prototype containing selected public source files and
examples. It does not
contain enough code or data to reconstruct the private system. It is not a
hosted service or a production security product, and has no model-provider
affiliation or endorsement. Public examples do not establish the reliability
of the unseen private workbench.

## Develop and contribute

A useful contribution can be small: an input that exposes a mistaken check,
a clearer explanation, an easier first command or an improvement to one tool.
[Contributing](CONTRIBUTING.md) explains how to report a reproducible mismatch,
test the first-use instructions or propose an infrastructure change. Mathematical
contributions belong in the [companion repository](https://github.com/wcook04/plectis-erdos/blob/main/CONTRIBUTING.md).

From the clone root:

```bash
make check   # fast registry and Lean-source checks; no installation
make ci      # tests, command smoke tests and a fresh package installation
```

`make ci` creates temporary environments and installs build and test
dependencies, so it may need network access. `make help` lists narrower checks.
Maintainers can run every registered public example with `make component-replays`
and recheck the task and saved-result calculations with
`make verify-operations DAFNY=/path/to/dafny`. Run
`make verify-components DAFNY=/path/to/dafny` for the twelve additional proved calculations.
The [validation guide](docs/maintainers/validation.md) explains dependencies,
release records and generated files. Edit their source and run the owning
builder rather than changing generated maps or recorded results by hand.
The [release review](RELEASE_REVIEW.md) records the candidate’s checks;
[source status](SOURCE_STATUS.md) explains which source material is included.

## Videos and related projects

Watch [Practical formal verification](https://www.youtube.com/watch?v=u3dad1v-o8c)
to see the component map and what the proofs cover. The
[introduction](https://www.youtube.com/watch?v=MBmVMMogXTA) explains Will Cook's
projects. His [videos page](https://wcook04.github.io/#videos) also has walkthroughs
of One Checkout, Safety Core and the private Code Map tool.

### Where this toolkit fits

The Python components and experiments in this clone are one part of Plectis.
The related repositories have different jobs, with their own setup instructions
and evidence. Follow the project that matches what you want to read or run.

| Related project | Start there for |
|---|---|
| [Plectis Erdős](https://github.com/wcook04/plectis-erdos) · [research website](https://wcook04.github.io/practical-formal-verification/map/) | The current mathematical papers, Lean proofs and open questions. |
| [Plectis Erdős Lean](https://github.com/wcook04/plectis-erdos-lean) | Lean proof files and commands for checking them against separately written statements. |
| [Plectis Atlas](https://github.com/wcook04/plectis-atlas) · [website](https://wcook04.github.io/plectis-atlas/) | Read OpenAI's maths papers alongside attributed outside assessments and proof-checking reports. |
| [Safety Core](https://github.com/wcook04/safety-core) | Instructions and automatic checks for AI coding assistants, with a map of which files they apply to. |
| [One Checkout](https://github.com/wcook04/one-checkout) | Committing a reviewed patch while preserving other unfinished edits in the same checkout. |
| [Plectis Zenith](https://github.com/wcook04/plectis-zenith) | Experiments on AI testers, earlier mistakes and code repair, with saved results and replay instructions. |

Code Map and Demo Take are private tools; this clone does not install them.
The [home page](https://wcook04.github.io/) links all the public projects and videos.

## Name and history

**How this was built.** William Cook sets the direction and is responsible for
the public claims; AI coding agents write and maintain most of the code.
[PROVENANCE.md](PROVENANCE.md) records authorship and third-party sources.

The project was called Microcosm until 21 June 2026. It became Plectis to avoid
confusion with Southampton's earlier Microcosm hypermedia system, without
implying endorsement or affiliation. Old names remain in package imports,
output paths and historical records for compatibility with existing tools.

For private security reports, see [SECURITY.md](SECURITY.md). To cite the
software, use [CITATION.cff](CITATION.cff). Copyright 2026 William Cook;
licensed under Apache 2.0, with details in [LICENSE](LICENSE) and [NOTICE](NOTICE).

## Mathematics companion snapshot

The companion's [current results guide](https://github.com/wcook04/plectis-erdos/blob/main/docs/RESULTS.md)
owns its mathematical claims. This toolkit's recorded source and release links
are preserved in the [companion reference](docs/reference/lean-companion.md).
