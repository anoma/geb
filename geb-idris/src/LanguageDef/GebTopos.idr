module LanguageDef.GebTopos

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.ProgFinSet

%default total

-------------------------------------
-------------------------------------
---- First-order recursive types ----
-------------------------------------
-------------------------------------

public export
data PS1Obj : Type where
  PS1Fin : PFSObj -> PS1Obj
  PS1Fix : PFSEndoFunc -> PS1Obj
