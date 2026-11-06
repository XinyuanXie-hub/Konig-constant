<!-- Adapted from XinyuanXie-hub/cyclic-lsi-new, commit 4b4ff9a506c0aac696119542b76276238c14cb9b, under Apache-2.0. Mathematical statement and verification links changed for König; pictures omitted. -->

# The König constant is one

This project uses [Lean](https://lean-lang.org/), a programming language in which a computer can verify mathematical proofs, to verify the asymptotic König constant result of:

> Xinyuan Xie and Haonan Zhang,
> *The König constant is one*,
> [arXiv:2608.14817](https://arxiv.org/abs/2608.14817).

[Mathematical statement](#mathematical-statement) · [Verification](#verification)

## Mathematical statement

For a positive integer $n$ and Lebesgue-measurable functions $f,g:\mathbb R^n\to\mathbb R$ satisfying $|f(x)|\leq1$ and $|g(x)|\leq1$ for every $x$, define

```math
B_n(f,g)=\frac{1}{(\sqrt{2}\,\pi)^n}
\int_{\mathbb R^n}\int_{\mathbb R^n}
f(x)g(y)\exp\!\left(-\frac{\|x\|^2+\|y\|^2}{2}\right)
\sin\langle x,y\rangle\,dy\,dx,
```

where both integrals use Lebesgue measure. Let

```math
K=\sup\left\{B_n(f,g): n\geq1,\ f,g\text{ as above}\right\}.
```

<a id="theorem"></a>

**Theorem.** The asymptotic König constant is one:

```math
K=1.
```

## Verification

To verify the correctness of the theorem in Lean, one only needs to check that the statement and definitions in [Challenge.lean](Challenge.lean) match the [theorem](#theorem) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the **Actions** tab, then open the latest **Lean CI** run on `main`, or open the [workflow runs](https://github.com/XinyuanXie-hub/Konig-constant/actions/workflows/lean.yml?query=branch%3Amain) directly.
2. Click **Verify the Challenge against Solution**, then expand **Run Comparator with Lean, NanoDa, and con-ron**.
3. Check that the log reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.

Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.
