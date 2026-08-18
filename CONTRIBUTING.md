# Contributing to the InfinityCosmos Project

Thank you for your interest in contributing to the InfinityCosmos Project!
This guide provides detailed instructions on how to effectively and efficiently contribute to the project.

## Building the Project Locally

[elan](https://github.com/leanprover/elan) is the only prerequisite. It reads `lean-toolchain` and installs the Lean version named there on the first `lake` command; no separate Lean install is needed.

```bash
git clone https://github.com/emilyriehl/infinity-cosmos.git
cd infinity-cosmos
lake exe cache get   # download Mathlib's prebuilt files
lake build
```

Without `lake exe cache get`, `lake build` compiles Mathlib from source, which takes hours. Run it again after any change to `lake-manifest.json`, including a dependency bump pulled from `main`.

`lake build :blueprint` builds the blueprint declarations as well. The `Compile blueprint` workflow runs that target on every pull request.

A first build takes a few minutes and needs about 10 GB: 2.8 GB for the toolchain under `~/.elan`, and 7.6 GB for dependencies and build output under `.lake`.

## Project Coordination

The project is managed using a [GitHub project dashboard](https://github.com/users/emilyriehl/projects/2),
which tracks tasks through various stages, from assignment to completion.

## How to Contribute

Contributions to the project are made through GitHub pull requests (PRs) that correspond to specific tasks outlined in the project's issues.
The following instructions detail the process for claiming and completing tasks.

### 1. Task Identification

- Tasks are posted as GitHub issues and can be found in the `Unclaimed` column of the project dashboard.
- Each issue represents a specific task to be completed. The issue title and description contain relevant details and requirements.

### 2. Claiming a Task

- To claim a task, comment the single word `claim` on the relevant GitHub issue.
- If no other user is assigned, you will automatically be assigned to the task, and the issue will move to the `Claimed` column.
- You may only claim one task at a time. If you decide not to work on a task after claiming it, comment the single word `disclaim` on the issue. This will unassign you and return the issue to the `Unclaimed` column, making it available for others to claim.

### 3. Working on the Task

Once you are assigned to an issue, begin working on the corresponding task. You should create a new branch from the `main` branch to develop your solution.

### 4. Submitting a Pull Request

- When you are ready to submit your solution, create a PR from your working branch to the project’s `main` branch.
- After submitting the PR, comment `propose #PR_NUMBER` on the original issue. This links your PR to the task, and the task will move to the `In Progress` column on the dashboard.
- A task can only move to `In Progress` if it has been claimed by the user proposing the PR.
- A PR is by default considered to be awaiting review unless it is tagged as a draft of wip.

### 5. Withdrawing or Updating a PR

- If you need to withdraw your PR, comment the single phrase `withdraw #PR_NUMBER` on the issue. The task will return to the `Claimed` column, but you will remain assigned to the issue.
- To submit an updated PR after withdrawal, comment `propose #NEW_PR_NUMBER` following the same process outlined in step 4.

### 6. Task Completion

- Once the PR is approved and merged, the task will automatically move to the `Completed` column.
- If further adjustments are needed after merging, a new issue will be created to track additional work.

## List of Contributors

* Aristotle (Harmonic)
* [Dagur Asgeirsson](https://github.com/dagurtomas)
* [Anne Baanen](https://github.com/Vierkantor)
* [Alvaro Belmonte](https://github.com/AlvaroRBO)
* [Kevin Buzzard](https://github.com/kbuzzard)
* [Robin Carlier](http://github.com/robin-carlier)
* [Mario Carneiro](https://github.com/digama0)
* [Daniel Carranza](https://github.com/daniel-carranza)
* [Johan Commelin](https://github.com/jcommelin)
* Kunhong Du
* [Jon Eugster](https://github.com/joneugster)
* [Rida Hamadani](https://github.com/Rida-Hamadani)
* [Julian Komaromy](https://github.com/juliankom)
* [Aaron Liu](https://github.com/plp127)
* [Arnoud van der Leer](https://github.com/arnoudvanderleer)
* [Jack McKoen](https://github.com/mckoen)
* [Bhavik Mehta](https://github.com/b-mehta)
* [Yuma Mizuno](https://github.com/yuma-mizuno)
* [Pietro Monticone](https://github.com/pitmonticone)
* [Thomas Murrills](https://github.com/thorimur)
* [Matej Penciak](https://github.com/mpenciak)
* [Nima Rasekh](https://github.com/nimarasekh)
* [Emily Riehl](https://github.com/emilyriehl)
* [Joël Riou](https://github.com/joelriou)
* [Robert Sneiderman](https://github.com/Robby955)
* [Alejandro José Soto Franco](https://github.com/alejandro-soto-franco)
* [Joseph Tooby-Smith](https://github.com/jstoobysmith)
* [Adam Topaz](https://github.com/adamtopaz)
* [Dominic Verity](https://github.com/dom-verity)
* [Nick Ward](https://github.com/gio256)
* [Andrew Yang](https://github.com/erdOne)
* [Zeyi Zhao](https://github.com/Georjez)
* [Thomas Zhu](https://github.com/hanwenzhu)
* [Serhii Khoma](https://github.com/srghma)
