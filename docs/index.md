---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

{% include mathjax.html %}

# Lean Bourgain

The purpose of this repository is to formalize the Bourgain extractor \[Bou05\], and as a part of that Szemeredi-Trotter in finite fields (\[BKT04\]),
in Lean 4.

## The source

Most definitions, theorems and proofs in this project have been taken from \[Dvi12\].

Additionally, some proofs were taken from the course "Selected Topics in Pseudorandomess" in Ben-Gurion University of the Negev, which exposed me to this subject and this formalization was a project for, and the proofs about the generalized XOR lemma were taken from \[Rao07\].

I remember seeing the proof used for showing every source is a convex combination of flat sources, by repeatedly taking a flat source of the highest K values with the maximum possibile coefficient, in some paper, but I couldn't locate it. If anyone is aware where this proof appeared, please inform me.

## The result

The final result of this project is [bourgain_extractor_final](https://command-master.github.io/lean-bourgain/docs/Pseudorandom/Bourgain.html#bourgain_extractor_final), which states that for any prime $$p$$, not equal to 2, and any positive integer $$m$$, the function $$f(x, y) = (xy + x^2 y^2 \bmod p) \bmod{m}$$ is a two source extractor, with
$$k = (1/2 - 1/35686629198734977) \log(p),$$ 
and $$\varepsilon = C p^{-1/2283944268719038528} \sqrt{m} (3 \ln(p) + 3) + \frac{m}{2p},$$ where $$C = \left( 16 \left(\sqrt{2\left((4\sqrt{16(2^{49}+2) + 5} + 92)^{1/4} + \frac{\sqrt2}4\right)} + 1\right) + 1\right)^{1/64} \approx 1.09 .$$
It can be noted that these values are quite worse than what appears in the literature, which I believe is mostly due to not attempting to optimize them at all.

## Acknowledgements

I'd like to thank Dean Doron for introducting me to this interesting subject, pointing me to the relevant papers, and helping with anything I had trouble understanding in them.

I'd like to thank the Lean community for helping me with any problems I had with Lean.

Finally, I'd like to thank Yaël Dillies for [LeanAPAP](https://yaeldillies.github.io/LeanAPAP/), whose results on discrete analysis had been extremely helpful.

## Infrastructure

The infrastructure for this webpage was mostly taken from [LeanAPAP](https://yaeldillies.github.io/LeanAPAP/) and [PFR](https://teorth.github.io/pfr/).

## Sources

\[Bou05\]: Bourgain, J. (2005). MORE ON THE SUM-PRODUCT PHENOMENON IN PRIME FIELDS AND ITS APPLICATIONS. International Journal of Number Theory, 01, 1-32.

\[BKT04\]: Bourgain, J., Katz, N.H., & Tao, T. (2004). A sum-product estimate in finite fields, and applications. Geometric & Functional Analysis GAFA, 14, 27-57.

\[Dvi12\]: Dvir, Z. (2012). Incidence Theorems and Their Applications. Found. Trends Theor. Comput. Sci., 6, 257-393.

\[Rao07\]: Rao, A. (2007). An Exposition of Bourgain's 2-Source Extractor. Electron. Colloquium Comput. Complex., TR07.