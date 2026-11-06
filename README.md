<!-- Adapted from XinyuanXie-hub/cyclic-lsi-new, commit 4b4ff9a506c0aac696119542b76276238c14cb9b, under Apache-2.0. Mathematical statement and verification links changed for König; pictures omitted. -->

# The König constant is one

This project uses Lean to verify that the König constant is one, the main result of the paper cited below.

> Xinyuan Xie and Haonan Zhang,
> *The König constant is one*,
> [arXiv:2608.14817](https://arxiv.org/abs/2608.14817).

## Mathematical statement

Let $`n`$ be a positive integer, and let $`f,g:\mathbb R^n\to\mathbb R`$ be Lebesgue-measurable functions satisfying $`|f(x)|\leq1`$ and $`|g(x)|\leq1`$ for every $`x\in\mathbb R^n`$. We define the normalized König bilinear form by

```math
B_{\mathrm K}(f,g):=\frac{1}{(\sqrt{2}\,\pi)^n}
\int_{\mathbb R^n}\int_{\mathbb R^n}
f(x)g(y)e^{-(\|x\|^2+\|y\|^2)/2}
\sin\langle x,y\rangle\,dy\,dx,
```

where both integrals are taken with respect to Lebesgue measure.

<a name="theorem-1"></a>

**Theorem 1.** The König constant is one:

```math
\mathfrak K_{\mathrm K}:=
\sup_{\substack{n\in\mathbb N\\n\geq1}}
\sup_{\substack{f,g:\mathbb R^n\to\mathbb R\ \text{Lebesgue-measurable}\\
|f(x)|\leq1,\ |g(x)|\leq1\ \text{for every }x\in\mathbb R^n}}
B_{\mathrm K}(f,g)=1.
```

## Verification

To verify the correctness of the theorem in Lean, one only needs to check that the statement and definitions in [Challenge.lean](Challenge.lean) match [Theorem 1](#theorem-1) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the first workflow run listed there, or open it directly from [here](https://xinyuanxie-hub.github.io/Konig-constant/latest-run/).
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the log reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!` (lines 591–596 of the complete downloaded job log for [this verified run](https://github.com/XinyuanXie-hub/Konig-constant/actions/runs/42155797780/job/127689507084); line numbers may vary between runs).

Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.
