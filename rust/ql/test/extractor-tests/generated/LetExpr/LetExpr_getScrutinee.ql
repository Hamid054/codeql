// generated by codegen, do not edit
import codeql.rust.elements
import TestUtils

from LetExpr x
where toBeTested(x) and not x.isUnknown()
select x, x.getScrutinee()
