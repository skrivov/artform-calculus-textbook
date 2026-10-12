import ArtformRoles.Calculus.Syntax
import ArtformRoles.Calculus.Effect
import ArtformRoles.Calculus.Signature
import ArtformRoles.Calculus.Reduction
import ArtformRoles.Calculus.Typing
import ArtformRoles.Calculus.Confluence
import ArtformRoles.Calculus.Injectivity
import ArtformRoles.Calculus.Scope
import ArtformRoles.Calculus.Telescope
import ArtformRoles.Calculus.SigFacts
import ArtformRoles.Calculus.Rename
import ArtformRoles.Calculus.Weaken
import ArtformRoles.Calculus.Subst
import ArtformRoles.Calculus.Inversion
import ArtformRoles.Calculus.TelFacts
import ArtformRoles.Calculus.SigWeaken
import ArtformRoles.Calculus.Preservation
import ArtformRoles.Calculus.Skeleton
import ArtformRoles.Calculus.Principal
import ArtformRoles.Calculus.SN
import ArtformRoles.Calculus.Canonical
import ArtformRoles.Calculus.Paths
import ArtformRoles.Calculus.Adequacy
import ArtformRoles.Calculus.Records
import ArtformRoles.Calculus.Justified
import ArtformRoles.Calculus.Modules
import ArtformRoles.Calculus.Erasure
import ArtformRoles.Calculus.Accept
import ArtformRoles.Calculus.Book

/-!
# The calculus of Part II

The dependent calculus `RATT` of Part II of the paper *Five Roles for Artforms*:
its syntax, effects, signatures and judgments, reduction and confluence,
renaming and substitution with exact effects, subject reduction, role
functionality and principal effects, strong normalization, canonical forms,
effects as path semantics, static and dynamic gate adequacy, justified records,
the module and extension theorems, erasure to a role-free calculus, and the
book's examples written in the calculus.
-/
