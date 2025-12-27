module Core.PrettyPrint where

import Syntax
import Text.Printf (printf)

prettyPrint :: Value -> String
prettyPrint val = case collectRecords val of
    [] -> ""
    records -> renderTable records
  where
    collectRecords :: Value -> [(String, String)]
    collectRecords (VMrg v1 v2) = collectRecords v1 ++ collectRecords v2
    collectRecords (VRcd label v) = [(label, ppValue v)]
    collectRecords _ = []

    ppValue :: Value -> String
    ppValue VUnit = "()"
    ppValue (VInt n) = show n
    ppValue (VBool b) = show b
    ppValue (VString s) = show s
    ppValue (VClos v _) = "Closure<" ++ ppValue v ++ ", ...>"
    ppValue (VRcd label v) = "{" ++ label ++ " = " ++ ppValue v ++ "}"
    ppValue (VMrg v1 v2) = ppValue v1 ++ "; " ++ ppValue v2
    
    renderTable :: [(String, String)] -> String
    renderTable records =
        let maxKeyLen = maximum (map (length . fst) records)
            maxValLen = maximum (map (length . snd) records)
            totalWidth = maxKeyLen + maxValLen + 7 -- Account for borders and padding
            separator = replicate totalWidth '-'
            formatRow (key, val') = printf "| %-*s | %*s |" maxKeyLen key maxValLen val'
         in unlines $ separator : concatMap (\r -> [formatRow r, separator]) records
