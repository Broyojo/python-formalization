import PyLean.DiffCore
import PyLean.TextLibs.StructDiff
import PyLean.TextLibs.BinasciiDiff
import PyLean.TextLibs.CsvDiff
import PyLean.TextLibs.ReDiff
import PyLean.TextLibs.PathDiff
import PyLean.TextLibs.ShlexDiff
import PyLean.TextLibs.TextwrapDiff
import PyLean.TextLibs.QuopriDiff
import PyLean.TextLibs.HtmlDiff
import PyLean.TextLibs.DifflibDiff
import PyLean.TextLibs.EtreeDiff
import PyLean.TextLibs.UrlDiff
import PyLean.TextLibs.TomlDiff

/-! Differential-testing handler for `textlibs` cases (`"mod": "textlibs"`).
The function name's prefix (`struct.`, `binascii.`, ...) selects the sub-handler. -/

namespace PyLean.TextLibs

open Lean PyLean PyLean.Diff

def run (fn : String) (j : Json) : Except String Json :=
  if fn.startsWith "struct." then Struct.run fn j
  else if fn.startsWith "binascii." || fn.startsWith "base64." then Binascii.run fn j
  else if fn.startsWith "csv." then Csv.run fn j
  else if fn.startsWith "re." then Re.run fn j
  else if fn.startsWith "path." then Path.run fn j
  else if fn.startsWith "shlex." then Shlex.run fn j
  else if fn.startsWith "textwrap." then Textwrap.run fn j
  else if fn.startsWith "quopri." then Quopri.run fn j
  else if fn.startsWith "html." then Html.run fn j
  else if fn.startsWith "difflib." then Difflib.run fn j
  else if fn.startsWith "etree." then Etree.run fn j
  else if fn.startsWith "etreepath." then Etree.pathRun fn j
  else if fn.startsWith "etreeattrib." then Etree.attribRun j
  else if fn.startsWith "etreecopy." then Etree.copyRun j
  else if fn.startsWith "url." then Url.run fn j
  else if fn.startsWith "toml." then Toml.run fn j
  else throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.TextLibs
