# Algebraic geometry in Lean

Algebraic geometry experiments at graduate student level in the Lean theorem prover.
Written for [this workshop](https://sites.google.com/view/durhamcompalggeom/home). 

## Temporary ways to use Lean

You can temporarily use Codespaces or Gitpod if you don't want to install Lean locally.

### Using Codespaces

You can temporarily play with Lean using Github codespaces. This requires a Github account, and you can only use it for a limited amount of time each month. If you are signed in to Github, click here:

<a href='https://codespaces.new/kbuzzard/DurhamAlgGeom2024' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

* Make sure the Machine type is `4-core`, and then press `Create codespace`
* After 1-2 minutes you see a VSCode window in your browser. However, it is still busily downloading mathlib in the background, so give it another few minutes (5 to be safe) and then open a `.lean` file to start.

### Using Gitpod

Gitpod is an alternative to codespaces that is slightly inconvenient, since it may require you to verify your phone number.

Click this button to get started:

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/kbuzzard/DurhamAlgGeom2024)

This creates a virtual machine in the cloud,
and installs Lean and Mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get!` as above.

Gitpod gives you 50 free hours every month.
When you are done working, choose `Stop workspace` from the menu on the left.
The workspace should also stop automatically
30 minutes after the last interaction or 3 minutes after closing the tab.

To restart a previous workspace, go to [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).

## Installation of Lean locally

If you don't want to use these web-based solutions, you can install Lean onto your computer.

* You have to install Lean, and two supporting programs: Git and VSCode. Follow these [instructions](https://docs.lean-lang.org/lean4/doc/quickstart.html) to do this.

* This will guide you to install VSCode (a text editor which supports Lean), git (a version control system) and elan (the Lean package manager).

* (On Windows, antivirus programs can cause slowdowns or errors when downloading a Lean project. Consider temporarily disabling your antivirus program in the step *Set up Lean 4 project*)

* In the step **Set up Lean 4 project** click on **Download an existing project** (third bullet point). Choose `Git repository URL`, enter `https://github.com/kbuzzard/DurhamAlgGeom2024` and then select a folder where you want to download this repository, and specify a folder name. Then press `Create project folder` and wait a few minutes.

* When you have downloaded the repository a message appears allowing you to open the project folder.
To test that everything is working, open the repository and open the file `DurhamAlgGeom2024/Tutorial/00Test.lean`. The file should be ready a few seconds later. If you see a blue squiggle under `#eval`, Lean is running correctly.

* A useful (but optional) extension is the VSCode extension `Error Lens`. If you install this, you will see messages from Lean right in the file where you're typing.

## Troubleshooting

Note: To get this repository, you will need to download Lean's mathematical library, which takes about 5 GB of storage space.

It might be tricky to get Lean running on a laptop that is more than 10 years old or on a chromebook, since Lean does use a moderate amount of resourses.
You can still run Lean in your browser by using Codespaces or Gitpod, see the the instructions above.

* If you get errors such as `curl: (35) schannel` or `uncaught exception: no such file or directory (error code: 2)` take a look [here](https://leanprover-community.github.io/install/project.html#troubleshooting).

## Update repository

If you want to get the latest version of this repository (e.g. the latest exercises), then you can pull the changes.

You can do this either via a terminal (`git pull`)
or via VSCode, in the `Source Control` tab (third icon in the top-left, or `ctrl+shift+G`/`cmd+shift+G`),
under `⋯` (More actions) you can click `Pull` to get the latest changes.

Note: you should *not* press `Sync`, since that will try to upload your changes to the assignment files to Github (you don't have the rights to do this).

## Links

* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
* [Formalizing mathematics 2024](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/)
* [Lean website](https://www.lean-lang.org/)
* [Mathlib website](https://leanprover-community.github.io/)
* [Topics in Mathlib](https://leanprover-community.github.io/mathlib-overview.html)
* [latest Mathlib API documentation](https://leanprover-community.github.io/mathlib4_docs/)

Some exciting projects using Lean:

* Interesting finished Lean projects: [Liquid Tensor Experiment](https://github.com/leanprover-community/lean-liquid), [Polynomial Freiman-Ruzsa Conjecture](https://teorth.github.io/pfr/), [Independence of the continuum hypothesis](https://flypitch.github.io/)
* Interesting ongoing Lean projects [Fermat's Last Theorem](https://imperialcollegelondon.github.io/FLT/), [Carleson's theorem](https://florisvandoorn.com/carleson/), [Equational Theories project](https://teorth.github.io/equational_theories/)
* [AlphaProof](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/) did well at the international mathematics olympiad using Lean.
