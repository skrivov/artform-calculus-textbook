"""How the LaTeX package listings prints each non-ASCII character of Lean.

listings cannot print Unicode under pdflatex, so every non-ASCII character a
printed listing contains needs an entry here; `literate()` writes the entries
a set of texts uses. The guide's extractor and the review sheets share this
table. An unmapped character stops either tool, so that no symbol is lost.
"""

GLYPHS = {
    # logic and order
    "¬": r"$\neg$", "∀": r"$\forall$", "∃": r"$\exists$", "∧": r"$\wedge$",
    "∨": r"$\vee$", "→": r"$\to$", "←": r"$\leftarrow$", "↔": r"$\leftrightarrow$",
    "⇒": r"$\Rightarrow$", "⇔": r"$\Leftrightarrow$", "↦": r"$\mapsto$",
    "≠": r"$\neq$", "≤": r"$\le$", "≥": r"$\ge$", "≈": r"$\approx$",
    "≃": r"$\simeq$", "≅": r"$\cong$", "≡": r"$\equiv$", "∣": r"$\mid$",
    "⊤": r"$\top$", "⊥": r"$\bot$", "⊢": r"$\vdash$", "∎": r"$\blacksquare$",
    # sets and operations
    "∈": r"$\in$", "∉": r"$\notin$", "⊆": r"$\subseteq$", "⊂": r"$\subset$",
    "⊇": r"$\supseteq$", "∩": r"$\cap$", "∪": r"$\cup$", "∅": r"$\emptyset$",
    "×": r"$\times$", "·": r"$\cdot$", "•": r"$\bullet$", "∘": r"$\circ$",
    "⊕": r"$\oplus$", "⊗": r"$\otimes$", "∑": r"$\Sigma$", "∏": r"$\Pi$",
    "⨆": r"$\bigsqcup$", "⨅": r"$\sqcap$", "⊔": r"$\sqcup$", "⊓": r"$\sqcap$",
    "∫": r"$\int$", "∞": r"$\infty$", "√": r"$\surd$", "∂": r"$\partial$",
    "≫": r"$\gg$", "⟶": r"$\longrightarrow$", "⥤": r"$\Rightarrow$",
    "⊣": r"$\dashv$", "⋙": r"$\ggg$", "⋃": r"$\bigcup$", "⋂": r"$\bigcap$",
    "⟦": r"$[\![$", "⟧": r"$]\!]$",
    "⋯": r"{\color{ArtGray}$\cdots$}", "…": r"$\ldots$", "▸": r"$\blacktriangleright$",
    "⟨": r"$\langle$", "⟩": r"$\rangle$", "‹": r"$\langle$", "›": r"$\rangle$",
    "⌊": r"$\lfloor$", "⌋": r"$\rfloor$", "⌈": r"$\lceil$", "⌉": r"$\rceil$",
    "‖": r"$\|$", "↑": r"$\uparrow$", "⇑": r"$\Uparrow$", "∠": r"$\angle$",
    "⁅": r"$[\![$", "⁆": r"$]\!]$", "†": r"$\dagger$", "★": r"$\star$",
    "⦃": r"$\{\!|$", "⦄": r"$|\!\}$", "⨯": r"$\times$", "⬝": r"$\cdot$", "∙": r"$\centerdot$",
    "↥": r"$\uparrow$", "↧": r"$\downarrow$", "≍": r"$\asymp$",
    "²": r"$^2$", "³": r"$^3$", "⁻": r"$^-$", "¹": r"$^1$", "⁰": r"$^0$",
    "ᵀ": r"$^{\mathsf T}$", "ᶜ": r"$^{c}$", "ᵒ": r"$^{o}$", "ᵖ": r"$^{p}$",
    "ˢ": r"$^{s}$", "ᴴ": r"$^{H}$", "ᵐ": r"$^{m}$", "ᵃ": r"$^{a}$",
    "ˣ": r"$^{\times}$", "ᶠ": r"$^{f}$",
    # subscripts
    "₀": r"$_0$", "₁": r"$_1$", "₂": r"$_2$", "₃": r"$_3$", "₄": r"$_4$",
    "₅": r"$_5$", "₆": r"$_6$", "₇": r"$_7$", "₈": r"$_8$", "₉": r"$_9$",
    "ₐ": r"$_a$", "ₑ": r"$_e$", "ᵢ": r"$_i$", "ⱼ": r"$_j$", "ₖ": r"$_k$",
    "ₗ": r"$_l$", "ₘ": r"$_m$", "ₙ": r"$_n$", "ₚ": r"$_p$", "ₛ": r"$_s$",
    "ₜ": r"$_t$", "ₓ": r"$_x$", "₊": r"$_+$", "₋": r"$_-$", "ᵥ": r"$_v$",
    # letters
    "ℕ": r"$\mathbb{N}$", "ℤ": r"$\mathbb{Z}$", "ℚ": r"$\mathbb{Q}$",
    "ℝ": r"$\mathbb{R}$", "ℂ": r"$\mathbb{C}$", "𝟙": r"$\mathbf{1}$",
    "ℓ": r"$\ell$", "ℏ": r"$\hbar$", "𝒰": r"$\mathcal{U}$", "𝒯": r"$\mathcal{T}$",
    "𝒞": r"$\mathcal{C}$", "𝒜": r"$\mathcal{A}$", "𝒢": r"$\mathcal{G}$", "𝓢": r"$\mathcal{S}$",
    "α": r"$\alpha$", "β": r"$\beta$", "γ": r"$\gamma$", "δ": r"$\delta$",
    "ε": r"$\varepsilon$", "ζ": r"$\zeta$", "η": r"$\eta$", "θ": r"$\theta$",
    "ϑ": r"$\vartheta$", "ι": r"$\iota$", "κ": r"$\kappa$", "λ": r"$\lambda$",
    "μ": r"$\mu$", "ν": r"$\nu$", "ξ": r"$\xi$", "π": r"$\pi$", "ρ": r"$\rho$",
    "σ": r"$\sigma$", "τ": r"$\tau$", "υ": r"$\upsilon$", "φ": r"$\varphi$",
    "ϕ": r"$\phi$", "χ": r"$\chi$", "ψ": r"$\psi$", "ω": r"$\omega$",
    "Γ": r"$\Gamma$", "Δ": r"$\Delta$", "Θ": r"$\Theta$", "Λ": r"$\Lambda$",
    "Ξ": r"$\Xi$", "Π": r"$\Pi$", "Σ": r"$\Sigma$", "Φ": r"$\Phi$",
    "Ψ": r"$\Psi$", "Ω": r"$\Omega$",
}


def unmapped(texts):
    """The non-ASCII characters of the texts that have no entry."""
    return sorted({ch for t in texts for ch in t if ord(ch) > 127} - set(GLYPHS))


def literate(texts, style="leanglyphs"):
    """A listings style that prints every non-ASCII character the texts use."""
    used = sorted({ch for t in texts for ch in t if ord(ch) > 127} & set(GLYPHS))
    table = " ".join("{%s}{{%s}}1" % (ch, GLYPHS[ch]) for ch in used)
    return "\\lstdefinestyle{%s}{literate=%s}\n" % (style, table)
