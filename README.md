# What this is and how to contribute

OpenAI's math write-ups can be difficult to understand and can have incomplete citations. This repo seeks to be an inclusive effort to improve these write-ups, and the broader math community--students, postdocs, professors, and enthusiasts--is invited to participate.

Three ways you can contribute:
1. Submit pull requests that augment lit reviews/cite related results where appropriate, improve exposition, and identify (and fix, if possible) any errors. The workflow is as follows.
    1. [Fork](https://docs.github.com/en/pull-requests/how-tos/work-with-forks/fork-a-repo) this repo.
    2. Make commits to your forked repo.
    3. [Submit a pull request](https://docs.github.com/en/pull-requests/how-tos/create-pull-requests/creating-a-pull-request-from-a-fork?utm_source=chatgpt.com).
   
    It is preferred you edit the TeX directly and compile it to `article.pdf` in subfolders of [`preprints/`](https://github.com/mathcommunity/oai-math-revised/tree/main/preprints). The full repository is large, so to work locally on a few papers you can do a sparse checkout that downloads only those papers; [docs/SPARSE_CHECKOUT.md](docs/SPARSE_CHECKOUT.md) explains how. Please disclose substantial use of automation (via language models, proof assistants, and other mathematical software) for your contributions. If you are unfamiliar with git and GitHub, [here is a helpful starting point](https://docs.github.com/en/get-started/start-your-journey/git-and-github-learning-resources).
2. Create an issue proposing changes to a write-up.
3. Add or modify a `NOTES.md` file in a subfolder of [`preprints/`](https://github.com/mathcommunity/oai-math-revised/tree/main/preprints) with sections for
    1. follow-up works (use links)
    2. constructive comments/reviews (use links; if they are difficult to access, reproduce with permission from authors as appropriate)
    3. list of people interested in meeting to work on digestion (add only your name or the name of anyone whose explicit permission you have to add)

Note you do not have to doxx to contribute; you can sign up for an alt GitHub handle. All submissions will be reviewed.

## Original OAI readme

This repository contains mathematical manuscripts and supporting proof artifacts produced by an internal OpenAI model. 

As part of model development, we evaluate our models on open research problems. We expanded these evaluations after performance on our existing mathematical evaluations saturated. Some outputs build upon earlier results produced by the models.

This collection includes results at different stages of verification. Not all have accompanying Lean formalizations. We will continue to update this repository with Lean formalizations as we obtain them. 

Some of the unformalized results could have issues. We will endeavor to fix any such issues quickly.
We are also exploring community-hosted repositories for these materials. 

### Navigating the collection

The current catalogue contains 719 manuscripts organized into 372 families. A family groups related papers, which may include a principal result, companion arguments, consequences, or alternative proofs. Each family is classified by mathematical discipline.

- Start with the [overview](overview.pdf) for descriptions of the families.
- Use the [manuscript map](CONTENTS.md) to find individual papers and their supporting materials.
- The [`preprints/`](preprints/) directory contains PDFs, source files, and manuscript-specific citation and build instructions.
- The [Lean library](lean/README.md) and [formalization catalogue](lean/formalization.yaml) describe the available formal proofs, their associated papers, and verification configurations. See the [Comparator instructions](lean/ComparatorChallenges/README.md) for additional checking instructions. The repository has ~42% top-line results formalized.
- Updates to the repo are described in the [history](history.md).

#### Reasoning summaries

We are also releasing abridged summaries of the model's reasoning, covering the following results:

| Family | Subject |
|---|---|
| 007 | [Ordinary two-point correlations of multiplicative functions](reasoning_traces/ordinary-two-point-correlations.pdf) |
| 017 | [The irrationality exponent of π](reasoning_traces/irrationality-exponent-of-pi.pdf) |
| 087 | [Symmetric and general Mahler conjectures](reasoning_traces/symmetric-and-general-mahler-conjectures.pdf) |
| 102 | [Ordinary NP-hardness at the basic semidefinite threshold](reasoning_traces/basic-semidefinite-threshold-np-hardness.pdf) |
| 159 | [Quasipolynomial bounds for arithmetic progressions](reasoning_traces/quasipolynomial-arithmetic-progressions.pdf) |
| 197 | [Kaplansky's direct-finiteness conjecture in characteristic two](reasoning_traces/kaplansky-direct-finiteness-characteristic-two.pdf) |
| 221 | [The Mézard–Parisi formula for diluted spin glasses](reasoning_traces/mezard-parisi-formula.pdf) |
| 271 | [Spontaneous magnetization in the quantum Heisenberg ferromagnet](reasoning_traces/spontaneous-magnetization-quantum-heisenberg-ferromagnet.pdf) |
| 287 | [Isomorphism of free group factors](reasoning_traces/free-group-factor-isomorphism.pdf) |
| 362 | [The three-dimensional relativistic Vlasov–Maxwell system](reasoning_traces/relativistic-vlasov-maxwell.pdf) |


### How the results were produced

The vast majority of results were obtained with the same procedure using an unreleased internal OpenAI model. On average, each result used three hours of ChatGPT Pro thinking compute with that model. Over the course of the evaluation, the model was posed approximately 4,000 problems. Aggregating the output into result families and manuscripts and requiring an appropriate level of significance led to the catalog outlined above.

Exceptions to this fixed procedure include work on a zero-free region for the Riemann zeta function and proof of the Hodge Conjecture for CM abelian varieties. Additionally, the writeup for the Re(s) > 11/12 zero-free region for the Riemann zeta function was human edited for readability. 


### Versions and citations

We will preserve the public release history of this collection. Corrections and revisions will be recorded as new versions, with previously released versions remaining accessible. 

To cite the individual manuscript, use the BibTeX block in its directory. 
