import VersoBlueprint
import VersoManual.Bibliography

open Verso.Genre.Manual.Bibliography

namespace InfinityCosmosBlueprint.Bibliography

private def article (title : String) (authors : Array String) (venue : String) (year : Int)
    (volume : String := "") : Citable :=
  .article {
    title := .text title
    authors := authors.map (.text ·)
    journal := .text venue
    year
    month := none
    volume := .text volume
    number := .text ""
  }

@[bib "RiehlVerity:2022eo"]
def riehlVerity2022 : Citable :=
  article "Elements of ∞-Category Theory" #["Emily Riehl", "Dominic Verity"]
    "Cambridge University Press" 2022

@[bib "Street:1974ec"]
def street1974 : Citable :=
  article "Elementary cosmoi I" #["R. H. Street"]
    "Category Seminar, Lecture Notes in Mathematics 420" 1974 "420"

@[bib "EilenbergMaclane:1945gt"]
def eilenbergMacLane1945 : Citable :=
  article "General theory of natural equivalences" #["S. Eilenberg", "S. Mac Lane"]
    "Transactions of the American Mathematical Society" 1945 "58"

@[bib "BoardmanVogt:1973hi"]
def boardmanVogt1973 : Citable :=
  article "Homotopy Invariant Algebraic Structures on Topological Spaces"
    #["J. M. Boardman", "R. Vogt"] "Springer-Verlag, Lecture Notes in Mathematics 347" 1973 "347"

@[bib "Joyal:2002qk"]
def joyal2002 : Citable :=
  article "Quasi-categories and Kan complexes" #["André Joyal"]
    "Journal of Pure and Applied Algebra" 2002 "175"

@[bib "Joyal:2008tq"]
def joyal2008 : Citable :=
  article "The Theory of Quasi-Categories and its Applications" #["André Joyal"]
    "Centre de Recerca Matemàtica Barcelona, Quadern 45 vol. II" 2008

@[bib "Quillen:1967ha"]
def quillen1967 : Citable :=
  article "Homotopical Algebra" #["Daniel Quillen"]
    "Springer-Verlag, Lecture Notes in Mathematics 43" 1967 "43"

@[bib "Riehl:2016cc"]
def riehl2016 : Citable :=
  article "Category Theory in Context" #["Emily Riehl"] "Dover Publications" 2016

@[bib "Brown:1973ah"]
def brown1973 : Citable :=
  article "Abstract homotopy theory and generalized sheaf cohomology" #["K. S. Brown"]
    "Transactions of the American Mathematical Society" 1973 "186"

@[bib "Cruttwell:2008rr"]
def cruttwell2008 : Citable :=
  .thesis {
    title := .text "Normed Spaces and the Change of Base for Enriched Categories"
    author := .text "G. S. H. Cruttwell"
    year := 2008
    university := .text "Dalhousie University"
    degree := .text "PhD thesis"
  }

@[bib "BlumbergMandell:2011ak"]
def blumbergMandell2011 : Citable :=
  article "Algebraic K-theory and abstract homotopy theory" #["A. Blumberg", "M. Mandell"]
    "Advances in Mathematics" 2011 "226"

@[bib "EilenbergKelly:1966cc"]
def eilenbergKelly1966 : Citable :=
  article "Closed categories" #["S. Eilenberg", "G. M. Kelly"]
    "Proceedings of the Conference on Categorical Algebra" 1966

@[bib "Kelly:1974da"]
def kelly1974 : Citable :=
  article "Doctrinal Adjunction" #["G. M. Kelly"]
    "Category Seminar, Lecture Notes in Mathematics 420" 1974 "420"

@[bib "Kelly:1989eo"]
def kelly1989 : Citable :=
  article "Elementary observations on 2-categorical limits" #["G. M. Kelly"]
    "Bulletin of the Australian Mathematical Society" 1989 "49"

@[bib "GabrielZisman:1967cf"]
def gabrielZisman1967 : Citable :=
  article "Calculus of Fractions and Homotopy Theory" #["P. Gabriel", "M. Zisman"]
    "Springer-Verlag, Ergebnisse der Mathematik 35" 1967 "35"

end InfinityCosmosBlueprint.Bibliography
