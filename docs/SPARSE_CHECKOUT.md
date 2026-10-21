# Working on one paper locally (sparse checkout)

The full repository has about 135,000 files, most of them in the Lean library. If you only want to work on one or a few papers, a sparse checkout lets you use the usual git and GitHub workflow (fork, edit, commit, pull request) while downloading just those papers plus the files at the top of the repository. For one paper that is about 25 MB.

## 1. Fork the repository

On https://github.com/mathcommunity/oai-math-revised, click **Fork**. You need your own copy to open a pull request.

## 2. Clone your fork without the full contents

```sh
git clone --filter=blob:none --sparse https://github.com/YOUR-USERNAME/oai-math-revised.git
cd oai-math-revised
```

This checks out only the files at the top of the repository (README, `overview.pdf`, `CONTENTS.md` and so on). Other files are downloaded when you ask for them.

## 3. Choose the papers

Each paper has a folder under `preprints/`. Its name is the last part of the paper's page address on the [website](https://mathcommunity.github.io/oai-math-revised/), and the page's "Source on GitHub" link opens it. You can also search `CONTENTS.md`.

```sh
git sparse-checkout set preprints/A-C1-Counterexample-to-the-Entropy-Conjecture-September-25-2026
```

To work on more papers later:

```sh
git sparse-checkout add preprints/<another-paper-folder>
```

## 4. Edit the TeX

The sources are in the paper's `build/` folder. Some papers are a single file; others are split across subfolders such as `sections/` or `source/`. The main file is the one containing `\begin{document}`, usually `main.tex` or `paper.tex`.

## 5. Recompile the PDF

With a TeX installation (for example TeX Live), go to the folder that holds the main file and compile it:

```sh
cd preprints/<paper-folder>/build      # or build/source, if that's where the main file is
latexmk -pdf main.tex                  # use the main file's name
```

Then copy the new PDF over the PDF at the top of the paper's folder, keeping that file's name (often `paper.pdf` or `main.pdf`), and remove the build files:

```sh
cp main.pdf ../paper.pdf               # adjust both names to your paper
latexmk -C -bibtex                     # deletes the generated .aux, .bbl, .log, .pdf, ... files
```

## 6. Commit, push and open a pull request

```sh
git checkout -b my-change
git add preprints/<paper-folder>
git commit -m "Add missing citations to the C1 entropy counterexample"
git push -u origin my-change
```

Then open your fork on GitHub and click **Compare & pull request**. Please disclose substantial use of language models, proof assistants or other software.

## Keeping your fork up to date

Before starting new work, update your copy:

```sh
git remote add upstream https://github.com/mathcommunity/oai-math-revised.git   # only once
git checkout main
git pull upstream main
```

## Getting the whole repository

To turn the sparse checkout into a full one (this downloads everything):

```sh
git sparse-checkout disable
```
