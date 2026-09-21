# The finite spectrum of E1485

**Theorem.** A nonempty finite magma satisfying

\[
                    (y*x)*(x*(z*y))=x                 \tag{W}
\]

has order \(q^2\) or \(2q^2\), and every such order occurs.

The idea is to count translation fibers. Their sizes force every
nonminimum translation degree to have an exact half. Consequently the
degrees are \(r,2r,\ldots,2^m r\), and the order is \(r^2 2^m\).

## 1. Translation degrees and sharp edges

Let \(M\) be a nonempty finite model, with \(n=|M|\). Write
\(R(a)=\{a*x:x\in M\}\), \(C(a)=\{x*a:x\in M\}\), and
\(e\to a\) when \(a\in R(e)\).

We will use the dual law and two absorption identities:

\[
\begin{aligned}
 ((y*z)*x)*(x*y)&=x,                                    \tag{D}\\
 x*((x*y)*(y*z))&=x*y,\\
 ((x*y)*(y*z))*z&=y*z.                                  \tag{A}
\end{aligned}
\]

Here is a derivation. Write \(z=z_1*z_2\), possible by (W).
For \(w=y*z\), (W) gives \(y=(z_2*y)*w\), hence
\((w*x)*(x*y)=(w*x)*(x*((z_2*y)*w))=x\), proving (D).
For absorption, apply (D) twice:
\[
 x*((x*y)*(y*z))
 =\bigl(((y*z)*x)*(x*y)\bigr)*((x*y)*(y*z))=x*y.
\]
Reversing multiplication gives the other identity.

The laws also give
\[
             e\to a\quad\Longleftrightarrow\quad e\in C(a).
\]
Indeed, \(a=e*t\) implies \(e=((t*z)*e)*a\) by (D);
\(e=z*a\) implies \(a=e*(a*(t*z))\) by (W).
In particular every product gives a path \(e\to e*b\to b\).

Call \(e\to a\) **sharp** if \(e*(a*x)=a\) for all \(x\).
Equivalently, \((x*e)*a=e\) for all \(x\), by (W) and (D).

**Sharp neighbors exist.** Fix \(a\), and put \(P_b(t)=a*(t*b)\).
The laws give
\[
 P_b^2=P_b,\qquad P_b(u)=u\ \Longrightarrow\ P_b(P_c(u))=P_c(u).
\]
For completeness, (W) gives \((b*a)*P_b(t)=a\), and (D) then
gives idempotence. If \(P_b(u)=u\), absorption gives
\((b*a)*P_c(u)=a\), and (D) shows \(P_b(P_c(u))=P_c(u)\).
Apply one \(P_b\) for each \(b\in M\): previously obtained fixed-point
conditions are preserved, so the result is a common fixed point, a sharp
successor of \(a\). Reverse multiplication to obtain sharp predecessors.

**Sharp edges give rectangular coordinates.** For \(e\to a\), consider
\[
 \Phi:M\longrightarrow R(a)\times C(e),\qquad
 \Phi(x)=(a*x,x*e).
\]
Writing \(a=e*t\), (D) gives \((a*x)*(x*e)=x\), so \(\Phi\)
is injective. If the edge is sharp, its inverse is \((u,v)\mapsto u*v\):
for \(u=a*x\), \(v=y*e\), sharpness gives \(e*u=a\), \(v*a=e\), and
\[
 a*(u*v)=(e*u)*(u*(y*e))=u,\qquad
 (u*v)*e=((a*x)*v)*(v*a)=v.
\]

A sharp predecessor therefore identifies left translation at \(a\)
with projection onto \(R(a)\); every nonempty left fiber has size
\(n/|R(a)|\). Dually, every nonempty right fiber has size \(n/|C(a)|\).

For a sharp edge \(e\to a\), the fiber \(\{x:e*x=a\}\) is exactly
\(R(a)\): one inclusion is sharpness; for the other, (W) gives
\(x=(e*x)*(x*(z*e))=a*(x*(z*e))\), with arbitrary \(z\).
Thus \(|R(e)|\,|R(a)|=n\). The rectangle also gives
\(|C(e)|\,|R(a)|=n\), so row and column sizes agree everywhere.
Denote their common value by \(d(a)\), the **translation degree**.

We have proved:
\[
\begin{gathered}
 \text{each nonempty translation fiber at }a\text{ has size }n/d(a),\\
 e\to a\ \Longrightarrow\ d(e)d(a)\ge n,\qquad
 e\to a\text{ sharp}\ \Longrightarrow\ d(e)d(a)=n.
\end{gathered}
\]
Taking sharp neighbors shows that \(n/D\) occurs whenever \(D\) does.
Consequently the minimum and maximum degrees, \(r\) and \(s\), satisfy
\(rs=n\).

## 2. Two fibers fit into one

A path \(e\to a\to b\) is **bad** when \(e*b\ne a\).
Put \(t=e*b\). The return fibers
\[
 X=\{c:t*c=b\},\qquad Y=\{d:d*t=e\}
\]
are in bijection by \(F(c)=c*e\), with inverse \(F^{-1}(d)=b*d\).
Membership and the inverse identities follow directly from (W) and (D):
\[
\begin{array}{ll}
 t*c=b:\quad (c*e)*t=e,& b*(c*e)=c,\\
 d*t=e:\quad t*(b*d)=b,& (b*d)*e=d.
\end{array}
\]

The old fibers
\[
 A=\{c:a*c=b\}\subseteq X,\qquad B=\{d:d*a=e\}\subseteq Y
\]
each have size \(n/d(a)\). The inclusions follow from absorption:
write \(e=z*a\), \(b=a*w\), and use
\[
 ((z*a)*(a*c))*c=a*c,\qquad
 d*((d*a)*(a*w))=d*a.
\]
Moreover \(A\cap F^{-1}(B)=\varnothing\). Otherwise (D) gives
\(a=((c*e)*a)*(a*c)=e*b\), contradicting badness. Counting in \(X\)
therefore gives
\[
                    \frac{2n}{d(a)}\le\frac{n}{d(t)},
 \qquad\text{so}\qquad d(a)\ge2d(e*b).                 \tag{1}
\]

## 3. A minimal bad endpoint makes the halving exact

Fix a nonsharp edge \(e\to a\). Among the nonempty set
\(\{b\in R(a):e*b\ne a\}\), choose \(b\) of minimum degree.

If (1) were strict, the two disjoint subsets would not fill \(X\).
There would be a \(c\) with
\[
 (e*b)*c=b,\qquad a*c\ne b,\qquad (c*e)*a\ne e.
\]
Set \(b'=a*c\). The first identity gives \(b\to c\), so
\(a\to b\to c\) is another bad path. Applying (1) to it gives
\[
                         2d(b')\le d(b).
\]
But \(b'\) is a bad endpoint for the original edge as well:
if \(e*b'=a\), then (W) would give
\(e=(c*e)*(e*(a*c))=(c*e)*a\), a contradiction.
Thus \(b'\in R(a)\), \(e*b'\ne a\), and \(d(b')<d(b)\),
contrary to minimality. We conclude that
\[
          \text{every nonsharp }e\to a\text{ admits }b
          \text{ with }d(a)=2d(e*b).                  \tag{2}
\]

## 4. Finish the spectrum calculation

Let \(d(a)>r\), choose \(h\) of degree \(r\), and put \(e=h*a\).
Since \(h\to e\to a\),
\[
                       n\le r\,d(e)\le rs=n.
\]
Hence \(d(e)=s\). The edge \(e\to a\) cannot be sharp, since
\(s\,d(a)>sr=n\). By (2), \(d(a)/2\) occurs.

Every degree above \(r\) can therefore be halved. Iteration terminates
at \(r\), so every degree is \(r\) times a power of two. Halving the
maximum shows that the degree set is exactly
\(\{r,2r,\ldots,2^m r\}\). Finally
\[
                       n=rs=r^2 2^m,
\]
a square if \(m\) is even and twice a square if \(m\) is odd.

Conversely, on \(A\times A\) the operation
\[
                       (a,b)*(c,d)=(b,c)
\]
satisfies (W), giving every square order. Boolean NAND
\(x*y=\neg(x\land y)\) satisfies (W) on two elements.
Direct products preserve the law, giving every twice-square order.

This classifies possible orders, not all operations of a given order.
The empty magma also satisfies the law; include \(q=0\) if empty models
are allowed.

## Lean formalization

The complete proof is in the following modules. The first four use
namespace `WeakCentralGroupoid`; the public theorems use `Spectrum`.

| Part | Source |
| --- | --- |
| Sharp neighbors and rectangles | [Basic.lean](../equational_theories/Spectrum/WeakCentral/Basic.lean) |
| Uniform fibers and extremal degrees | [Finite.lean](../equational_theories/Spectrum/WeakCentral/Finite.lean) |
| Return matching and exact halving | [Halving.lean](../equational_theories/Spectrum/WeakCentral/Halving.lean) |
| Iterating halving and parity | [Dyadic.lean](../equational_theories/Spectrum/WeakCentral/Dyadic.lean) |
| Both directions of the spectrum theorem | [WeakCentralSpectrum.lean](../equational_theories/Spectrum/WeakCentralSpectrum.lean) |

The public declarations are `Spectrum.hasModel_1485_iff` (including zero)
and `Spectrum.spectrum_1485` (positive orders). The catalogue also
records the same spectrum for the equivalent law E2162.

The degree-support and spectrum theorems have `#guard_msgs` checks on
their axioms: exactly `propext`, `Classical.choice`, and `Quot.sound`.
There are no incomplete proofs or computational axioms.

Rebuild the theorem and run the catalogue/type/axiom checks:

```sh
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
lake env lean scripts/test_spectrum_status.lean
python3 scripts/spectrum_generate.py --check
```
