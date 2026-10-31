# M178 R2: four real affine latitude rows for simultaneous handedness success — UNREVIEWED

This is new manual research OUTSIDE the completed M177 cutoff, by the additional miscellaneous-duty Sol agent. It is a candidate reduction for ROOT review, not an independent acceptance of its own mathematics. Starting sources are corrected original force5edba7e6, M177 b0f73093 with99dcaf50 and distinct scoped review091c81c4, and the accepted remaining double-norm charts671583b8/792082ee/d71cff1b. Complete actual sources and scopes were read afresh after byte authentication. No CAS, numerical science, symbolic evaluator or scientific import was used.

## 1. Domain and the original force

Keep q>0,t=q²=103/2,c=1+t,R>0,u=1+R,Bc=1-iq,L=u-iqR. Use the ORIGINAL normal variables

    a=1-x, b=2-3a, s=K², D=3-s, h=as+b,
    N(s)=s²+nu s+kappa=0,
    nu=5-8a+6G, kappa=2b².

We work ONLY on the accepted remaining DOUBLE-NORM chart: G>0,0<R<52,rho!=0,Z!=0,d>0,Lambda>0,0<s=Pi/Lambda<3, its exact normal quartic F(Z)=0, h!=0 and both original phase determinants nonzero. All original reconstruction guards are retained. The radial quadratic and definitions of a,d,G,Lambda,Pi are exactly those in671583b8/792082ee. No result is claimed for other charts.

For gamma=±sqrt(G), original5edba gives

    Delta=d+4q gamma,
    T=p+iq j0+gamma(qu+im),
    p=ma-v, j0=1-ua,
    m=1+(2+3t)R+cR², v=1+cR.

Its phase is V=-2HT/Delta. The chart supplies the phase norm for BOTH signs and the nonzero determinant product, not their remaining full trace. For either sign, the complete ORIGINAL remaining trace is equivalent to J=0, with the corrected Bc factor and

    J=RD Delta Ahat+RsD Delta[Bhat-E(3+iq)]
         -2h Ahat T-2RhD Bhat barT,
    E=a-i gamma, Ahat=2LW.

This is exactly5edba(15); no new denominator clearing or source convention is installed. Both signs pass if and only if their two J values vanish.

## 2. Normal-locus simplifications before splitting signs

On the ORIGINAL normal equation,792082ee(12) gives

    W/s=w+i j gamma,
    j=1+s,
    w=w0+s w1,
    w0=3/2+a-3a², w1=a-1/2-G.

The complete Bhat from792082ee(11) is

    Bhat=Ub+iq Vb+gamma s(-3q+i),
    Ub=2s+b,
    Vb=b(4a-1)+s(4a-2-4G).

These are identities on the retained original normal locus; they are not extensions of a special singular-phase trace formula. Substitution in the ORIGINAL J gives

    J=sD R Delta F
         -4hs L(w+i j gamma)T
         -2RhD Bhat barT,
    F=2L(w+i j gamma)+Bhat-E(3+iq).

Define the following REAL quantities:

    f=2u w+Ub-3a,
    g=Vb-a-2Rw,
    alpha=2Rj-3s-1,
    beta=2uj+s+3.

Direct multiplication gives F=f+iq g+gamma(q alpha+i beta). In particular its odd real contribution from -E(3+iq) is -q gamma; the sign is retained.

## 3. Transparent product table

All quantities below are real polynomials in s at fixed R,a,G,t:

    Ce=w p-jmG,
    De=w j0+juG,
    Eo=wu-j j0,
    Fo=wm+jp,

    Ie=Ub p+t Vb j0+Gs(m-3tu),
    Je=Vb p-Ub j0+Gs(3m+u),
    Ko=Ub u+Vb m+s(j0-3p),
    Lo=tu Vb-m Ub+s(p+3t j0).

The two elementary products are exactly

    (w+i j gamma)T = Ce+iq De+gamma(q Eo+i Fo),
    Bhat barT       = Ie+iq Je+gamma(q Ko+i Lo),

using gamma²=G. For example the G contribution to the second product is
Gs(-3q+i)(qu-im)=Gs[m-3tu+iq(3m+u)], which checks both of its signs. Multiplication by L=u-iqR gives

    L(Ce+iq De)=(uCe+tRDe)+iq(uDe-RCe),
    L(q Eo+i Fo)=q(uEo+RFo)+i(uFo-tREo).

Finally Delta F has even part
d f+4tG alpha+iq(d g+4G beta)
and odd part
gamma{q(d alpha+4f)+i(d beta+4t g)}.
These displayed products are a manual derivation, not output of a symbolic evaluator.

## 4. Four scalar original-trace equations

Define four REAL polynomials

    Pe=sD R(d f+4tG alpha)
          -4hs(uCe+tRDe)-2RhD Ie,

    Qe=sD R(d g+4G beta)
          -4hs(uDe-RCe)-2RhD Je,

    Po=sD R(d alpha+4f)
          -4hs(uEo+RFo)-2RhD Ko,

    Qo=sD R(d beta+4t g)
          -4hs(uFo-tREo)-2RhD Lo.

Then, on N=0 and gamma²=G,

    J(gamma)=Pe+iq Qe+gamma(q Po+i Qo).

Because G>0 and q>0, adding and subtracting J(+sqrt(G)) and J(-sqrt(G)) proves the EXACT equivalence

    both original full traces vanish
       <=> Pe=Qe=Po=Qo=0.                         (A)

Neither Atr nor Btr, nor the affine U or C0 of b0f73093, has been assumed nonzero or divided out. This includes any U=C0=0 branch. The equivalence is asserted only with the original phase/norm/normal guards, not on every algebraic zero of these polynomials.

## 5. Monic normal reduction makes all four rows affine

At fixed R,a,G,t, the quantities w,j,Ub,Vb,f,g,alpha,beta and every product-table entry are affine or lower in s. Both h and D are affine. Consequently each of Pe,Qe,Po,Qo has degree AT MOST THREE in s. This degree claim refers to the real polynomials with d held at its actual latitude-independent chart value.

For any one of these four polynomials write

    P(s)=c3 s³+c2 s²+c1 s+c0.

No coefficient is assumed nonzero. Since the ORIGINAL normal polynomial is MONIC,

    s² = -nu s-kappa,
    s³ = (nu²-kappa)s+nu kappa    modulo N.

Thus define explicitly

    ell=c1-nu c2+(nu²-kappa)c3,
    n=c0-kappa c2+nu kappa c3.

On N=0 the original row P(s)=0 is equivalent to ell s+n=0. This reduction never divides by a polynomial coefficient, h,U,C0,Atr or Btr. Applying it to the four displayed polynomials yields real vectors ell=(ell1,...,ell4), n=(n1,...,n4) and

    both original full traces vanish
       <=> ell s+n=0, with the original N=0 and guards. (B)

The c_j are the coefficients of the explicitly displayed finite cubic products above, not unknown inverse data. The formulas specify finite polynomial arithmetic without a gamma square root. Coefficients depend only on R,a,G,t; after the accepted chart reconstruction they are explicit rational functions of R,rho,Z with its guarded denominators.

## 6. Rank alternatives and exact chart filter

The zero-row stratum is retained in full:

* If ell=0, BOTH signs pass the trace precisely when n=0. There is no proof here that this stratum is empty or incompatible with the accepted chart.
* If ell!=0, put L2=sum ell_i²>0 and Q=sum ell_i n_i. The four rows are equivalent to all six minors ell_i n_j-ell_j n_i=0 together with s=-Q/L2.

The latitude guard0<s<3 then becomes -3L2<Q<0. The original normal equation gives the necessary scalar identity

    Q²-nu Q L2+kappa L2²=0.

These guarded rank formulas are optional reorganizations of(B), not an exclusion of ell=0. In particular they do not justify dropping the earlier U=C0=0 exceptional branch.

On the already accepted normal chart, s=Pi/Lambda with Lambda>0. The most direct division-free simultaneous-sign test is simply

    Pi ell_i+Lambda n_i=0 for i=1,...,4,              (C)

jointly with the radial quadratic,F(Z)=0 and ALL original guards. Equation(C), unlike a quotient by U or Btr, includes every zero-row and exceptional affine branch. It is exactly equivalent to simultaneous full-force success in the remaining chart, not merely a phase-norm test.

## 7. What is and is not settled

This supplies a transparent ORIGINAL-trace sum/difference reduction with four real cubic rows and a monic-normal affine reduction. It gives an exact smaller-latitude feasibility/rank problem without assuming either signed filter coefficient nonzero. I have not established a sign contradiction or guard contradiction for(C), nor proved ell and n cannot vanish together.

The existing nonzero normal quartic still gives at most four Z roots per nonzero radial branch at each FIXED R, at most eight chart points and sixteen signed tuples before trace. This work does not improve that unconditional bound. In the exceptional simultaneous-sign set each surviving chart point contributes two signs; no new counting reduction is asserted without excluding or bounding the intersection.

The remaining problem is exactly the accepted radial-root equation, original normal quartic and guards, plus(C). Establishing absence of a common positive-radius component, emptiness of the zero-row stratum, or a nonzero eliminant requires further proof. Bounded0<R<52 and finite fixed-R fibres do not imply global finiteness. The admitted set also avoids open denominator strata; bounded chart coordinates alone do not supply positive uniform separation from their excluded divisors.

All mathematics is manual. New source calculation/description corrections0, metadata preparation0; all owned handles dead. Predecessor source and evidence families were frozen before semantics and remain unchanged. Extracted predecessor literals are distinguished from our exact current request/result records. No canonical ledger or textbook was edited. This unreviewed new research is outside M177 publication and does not alter its accepted scope or histories. No physical/quantum/full40/gravitational-parent conclusion follows; all eight routes remain active.

