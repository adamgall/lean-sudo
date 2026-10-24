import LeanSudo.I18n
import LeanSudo.I18n.Render
import LeanSudo.Cli

/-! Pure gettext tests use synthetic MO bytes, without host locale or gettext tools. -/
namespace Tests.I18n
open LeanSudo.I18n

private def u32 (big : Bool) (value : Nat) : ByteArray :=
  ⟨((List.range 4).map fun i => UInt8.ofNat (value / 256 ^ (if big then 3 - i else i) % 256)).toArray⟩

private def words (big : Bool) (values : List Nat) : ByteArray :=
  values.foldl (fun bytes n => bytes ++ u32 big n) ByteArray.empty

private def mo (big : Bool) (entries : List (String × String)) : ByteArray := Id.run do
  let base := 28 + entries.length * 16
  let mut originals := []
  let mut translations := []
  let mut payload := ByteArray.empty
  for (original, translated) in entries do
    let source := original.toUTF8
    originals := originals ++ [source.size, base + payload.size]
    payload := payload ++ source ++ ⟨#[0]⟩
    let target := translated.toUTF8
    translations := translations ++ [target.size, base + payload.size]
    payload := payload ++ target ++ ⟨#[0]⟩
  return words big [0x950412de, 0, entries.length, 28, 28 + 8 * entries.length, 0, 0] ++
    words big originals ++ words big translations ++ payload

private def replaceWord (bytes : ByteArray) (offset value : Nat) : ByteArray :=
  bytes.extract 0 offset ++ u32 false value ++ bytes.extract (offset + 4) bytes.size

private def nul : String := String.singleton '\x00'
private def pluralSource : String := "file" ++ nul ++ "files"
private def french : List (String × String) :=
  [("", "Content-Type: text/plain; charset=UTF-8\nPlural-Forms: nplurals=2; plural=(n > 1);\n"),
   ("hello", "héllô 世界"), (pluralSource, "fichier" ++ nul ++ "fichiers")]
private def catalog : Catalog := (parseMo (mo false french)).getD {}

#guard (parseMo (mo false [])).isSome
#guard (parseMo (mo true [])).isSome
#guard (parseMo (mo false french)).isSome
#guard parseMo (mo false french) == parseMo (mo true french)
#guard catalog.entries == french
#guard lookup catalog "hello" == "héllô 世界"
#guard lookup catalog "unknown %s" == "unknown %s"
#guard lookup {} "hello" == "hello"
#guard lookup { entries := [("blank", "")] } "blank" == "blank"
#guard nlookup {} "file" "files" 1 == "file"
#guard nlookup {} "file" "files" 0 == "files"
#guard nlookup catalog "file" "files" 0 == "fichier"
#guard nlookup catalog "file" "files" 1 == "fichier"
#guard nlookup catalog "file" "files" 2 == "fichiers"
#guard nlookup catalog "missing" "missings" 2 == "missings"
example (s : String) : lookup {} s = s := lookup_empty s
example (s : String) : lookup { entries := [] } s = s := lookup_absent _ _ rfl

-- Every strict prefix is truncated, including a missing final NUL terminator.
#guard (List.range (mo false french).size).all fun n =>
  (parseMo ((mo false french).extract 0 n)).isNone
#guard (parseMo ByteArray.empty).isNone
#guard (parseMo (replaceWord (mo false french) 0 0)).isNone
#guard (parseMo (replaceWord (mo false french) 4 0x20000)).isNone
#guard (parseMo (replaceWord (mo false french) 4 1)).isNone
#guard (parseMo (replaceWord (mo false french) 8 0xffffffff)).isNone
#guard (parseMo (replaceWord (mo false french) 12 0xffffffff)).isNone
#guard (parseMo (replaceWord (mo false french) 16 0xffffffff)).isNone
#guard (parseMo (replaceWord (mo false french) 28 0xffffffff)).isNone
#guard (parseMo (replaceWord (mo false french) 32 0xffffffff)).isNone
#guard (parseMo (replaceWord (replaceWord (mo false french) 20 4) 24 0xffffffff)).isNone
-- Strict UTF-8, rather than lossy replacement of malformed source/translation.
private def badUtf8 : ByteArray :=
  words false [0x950412de, 0, 1, 28, 36, 0, 0, 1, 44, 1, 46] ++ ⟨#[255, 0, 65, 0]⟩
#guard (parseMo badUtf8).isNone
#guard (parseMo (words false [0x950412de, 0, 1, 28, 36, 0, 0, 1, 44, 1, 46] ++
  ⟨#[65, 0, 255, 0]⟩)).isNone

private def value (text : String) (n : Nat) : Option Int :=
  (parsePlural text).map (·.eval n)
#guard value "n != 1" 0 == some 1
#guard value "n != 1" 1 == some 0
#guard value " n ? 2 : 3 " 0 == some 3
#guard value "n ? 2 : 3" 10 == some 2
#guard value "1 ? 0 ? 2 : 3 : 4" 0 == some 3
#guard value "0 ? 1 : 0 ? 2 : 3" 0 == some 3
#guard value "1 + 2 * 3 == 7 && 8 / 2 == 4 || 0" 0 == some 1
#guard value "(1 + 2) * 3" 0 == some 9
#guard value "10 - 3 - 2" 0 == some 5
#guard value "20 / 2 / 2" 0 == some 5
#guard value "!n + +2" 0 == some 3
#guard value "-7 / 3" 0 == some (-2)
#guard value "-7 % 3" 0 == some (-1)
#guard value "1 / 0 + 2 % 0" 0 == some 0
#guard value "0 && 1 / 0" 0 == some 0
#guard value "1 || 1 / 0" 0 == some 1
#guard value "n >= 2 && n <= 4 && n > 1 && n < 5" 3 == some 1
#guard value "n >= 2 && n <= 4 && n > 1 && n < 5" 9 == some 0
#guard ["", "n junk", "n ? 1", "n ? : 2", "(n", "n)", "n & 1", "n = 1", "n +"].all
  (fun s => (parsePlural s).isNone)

private def slavic : Catalog := (parseMo (mo true
  [("", "Plural-Forms: nplurals=3; plural=n%10==1 && n%100!=11 ? 0 : n%10>=2 && n%10<=4 && (n%100<10 || n%100>=20) ? 1 : 2;\n"),
   ("item" ++ nul ++ "items", "one" ++ nul ++ "few" ++ nul ++ "many")])).getD {}
#guard nlookup slavic "item" "items" 1 == "one"
#guard nlookup slavic "item" "items" 2 == "few"
#guard nlookup slavic "item" "items" 5 == "many"
#guard nlookup slavic "item" "items" 11 == "many"
#guard nlookup slavic "item" "items" 21 == "one"
#guard nlookup slavic "item" "items" 22 == "few"
#guard nlookup (merge catalog slavic) "file" "files" 0 == "fichier"
#guard nlookup (merge catalog slavic) "item" "items" 22 == "few"
#guard lookup (merge catalog { entries := [("hello", "wrong"), ("extra", "added")] }) "hello" == "héllô 世界"
#guard lookup (merge catalog { entries := [("extra", "added")] }) "extra" == "added"
private def invalidRule (rule : String) : Catalog := (parseMo (mo false
  [("", "Plural-Forms: " ++ rule ++ ";\n"), (pluralSource, "one" ++ nul ++ "many")])).getD {}
#guard nlookup (invalidRule "nplurals=0; plural=0") "file" "files" 2 == "many"
#guard nlookup (invalidRule "nplurals=2; plural=n +") "file" "files" 2 == "many"
#guard nlookup (invalidRule "nplurals=2; plural=5") "file" "files" 2 == "files"
#guard nlookup (invalidRule "nplurals=2; plural=-1") "file" "files" 1 == "file"
#guard nlookup { entries := [(pluralSource, "one" ++ nul)] } "file" "files" 2 == "files"
#guard nlookup { entries := [(pluralSource, "one")] } "file" "files" 2 == "files"

#guard format "plain text" [] == "plain text"
#guard format "%s: %d of %u (%%)" ["sudo", "-3", "42"] == "sudo: -3 of 42 (%)"
#guard format "%2$s then %1$s and %2$s" ["first", "second"] == "second then first and second"
#guard format "%2$05d %1$-6s!" ["abc", "-7"] == "-0007 abc   !"
#guard format "%+5d|% 5d|%-5u" ["2", "3", "4"] == "   +2|    3|4    "
#guard format "%08.4d" ["-12"] == "   -0012"
#guard format "%.3s %.0d" ["héllô", "0"] == "hél "
#guard format "%lld %zu %hhd %i" ["-1", "2", "3", "4"] == "-1 2 3 4"
#guard format "%s %s" ["one"] == "one %s"
#guard format "%n %q %" ["secret"] == "%n %q %"
#guard format "%0$s %9$s %s" ["safe"] == "%0$s %9$s safe"
#guard format "100%% %s" ["%n"] == "100% %n"
#guard format "%999999999s" ["safe"] == "%999999999s"
#guard format "%2$u/%1$d" ["-9", "12"] == "12/-9"

private def diagnostics : Catalog := {
  entries := [("", "Language: de\n"), ("Sorry, try again.", "Noch einmal."),
    ("%s is not in the sudoers file.\n", "»%s« fehlt.\n"),
    ("Matching Defaults entries for %s on %s:\n", "Vorgaben auf %2$s für %1$s:\n"),
    ("parsed OK", "korrekt"), ("untranslated %s", ""),
    ("%d incorrect password attempt" ++ nul ++ "%d incorrect password attempts",
      "%d Fehlversuch" ++ nul ++ "%d Fehlversuche")] }

#guard LeanSudo.I18n.render {} "sudo: raw %s\n\n" == "sudo: raw %s\n\n"
#guard LeanSudo.I18n.render diagnostics "" == ""
#guard LeanSudo.I18n.render diagnostics "\n\n" == "\n\n"
#guard LeanSudo.I18n.render diagnostics "sudo: Sorry, try again.\n" == "sudo: Noch einmal.\n"
#guard LeanSudo.I18n.render diagnostics "bob is not in the sudoers file.\n" == "»bob« fehlt.\n"
#guard LeanSudo.I18n.render diagnostics "Matching Defaults entries for alice on host:\n\n" ==
  "Vorgaben auf host für alice:\n\n"
#guard LeanSudo.I18n.render diagnostics "/etc/sudoers: parsed OK\n" == "/etc/sudoers: korrekt\n"
#guard LeanSudo.I18n.render diagnostics "sudo: 3 incorrect password attempts\n" == "sudo: 3 Fehlversuche\n"
#guard LeanSudo.I18n.render diagnostics "untranslated value\n" == "untranslated value\n"
#guard format "%c %o %x" ["q", "440", "ff"] == "q 440 ff"
#guard ((LeanSudo.Cli.helpFor "sudo" {
  entries := [("use a helper program for password prompting", "translated prompt help")] }).splitOn "\n").contains
    "  -A, --askpass                 translated prompt help"
#guard ((LeanSudo.Cli.helpFor "sudo" {
  entries := [("in list mode, display privileges for user",
    "im Aufzählungsmodus, Rechte des Nutzers anzeigen")] }).splitOn "\n").contains
    "  -U, --other-user=user         im Aufzählungsmodus, Rechte des Nutzers"

end Tests.I18n
