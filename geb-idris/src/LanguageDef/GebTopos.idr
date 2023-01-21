module LanguageDef.GebTopos

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.ProgFinSet
import public LanguageDef.PolyCat

%default total

public export
MorphSig : SliceObj Type
MorphSig x = SliceObj (x, x)

public export
MorphSPF : Type -> Type
MorphSPF x = DepParamPolyFunc (x, x) (x, x)

public export
MorphMu : {x : Type} -> MorphSPF x -> MorphSig x
MorphMu {x} = SPFMu . SPFFromDPPF
