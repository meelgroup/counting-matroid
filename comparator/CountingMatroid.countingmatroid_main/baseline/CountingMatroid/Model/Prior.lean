/-!
# What this development assumes

The results this proof takes from prior work — cited, standard, or folklore —
stated as the hypotheses they are. `Prior` is a field per borrowed result, and the
theorem carries it as `(hprior : Prior)`, so what was granted is in the statement
rather than in a `sorry` somewhere under it.

When a later theorem needs assumptions the earlier theorems do not need, this
file may also hold another theorem-specific structure. Existing structures are
not widened just to state a new result.

It is empty because nothing has been surveyed yet. The pass that reads the
paper for what the proof leans on fills it in; until then the theorem assumes
nothing and `hprior` is discharged by `⟨⟩`.
-/

namespace CountingMatroid

/-- Every result this development takes from prior work rather than proving. -/
-- TEX2LEAN: external-prior fields
structure Prior : Prop where

end CountingMatroid
