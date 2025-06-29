import Snippets.ContT

def Rec := Dynamic → ContT Unit IO Dynamic

deriving instance TypeName for Rec

def get : Dynamic → IO Rec := fun d =>
  match d.get? Rec with
  | .some r => pure r
  | .none => panic! "Oups!"

def toRec : (Rec → ContT Unit IO Rec) → Rec := fun k d =>
  do
    let r ← get d
    let r' ← k r
    pure <| Dynamic.mk r'

def yin : ContT Unit IO Rec :=
  do
    let (k : Rec) ← callCC (fun k => pure <| toRec k)
    IO.println ""
    pure k

def yang : ContT Unit IO Rec :=
  do
    let (k : Rec) ← callCC (fun k => pure <| toRec k)
    IO.print "*"
    pure k

def yinyang : ContT Unit IO Rec :=
  do
    let k ← yin
    let k' ← yang
    let (d : Dynamic) ← k (Dynamic.mk k')
    let r ← get d
    pure r

def main (_ : List String) : IO UInt32 := do
   run (fun _ => pure ()) yinyang
   return 0
