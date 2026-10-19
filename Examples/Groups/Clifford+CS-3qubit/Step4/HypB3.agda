------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
-- 
-- Part 3 of 5 of the proofs of Step4.Main's hypB that compute normal
-- forms, one lemma per relation of Step 3; in one module they took 41 s.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Presentation.Tactics.Lists
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words

open Monoid-Equational
open Rewriting
open Associative
open InContext

open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)
open import Examples.Groups.Clifford+CS-3qubit.MaybeEq-Instances
open import Examples.Groups.Clifford+CS-3qubit.CosetNF
open import Examples.Groups.Clifford+CS-3qubit.Gate

import Examples.Groups.Clifford+CS-3qubit.Step3.Rel as L

open import Examples.Groups.Clifford+CS-3qubit.Step4.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8D
open import Examples.Groups.Clifford+CS-3qubit.Step4.KD
open import Examples.Groups.Clifford+CS-3qubit.Step4.Lemmas

open import Examples.Groups.Clifford+CS-3qubit.Step4.Simple

module Examples.Groups.Clifford+CS-3qubit.Step4.HypB3 where

  hb1876 : Goal L.ax-CCZ-K0-CK20-CK10=K0-CK20-CK10-CCX0
  hb1876 = ListNF.listnfeq' nf-e4 auto

  hb1877 : Goal L.ax-CCZ-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCZ
  hb1877 = ListNF.listnfeq' nf-e4 auto

  hb1878 : Goal L.ax-CCZ-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb1878 = ListNF.listnfeq' nf-e4 auto

  hb1879 : Goal L.ax-CCZ-K0-CK20-CCK'=K0-CK20-CCK'-CCX0-CS12-CCZ
  hb1879 = ListNF.listnfeq' nf-e4 auto

  hb1880 : Goal L.ax-CCZ-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CCX0
  hb1880 = ListNF.listnfeq' nf-e4 auto

  hb1881 : Goal L.ax-CCZ-K0-CCK'=K0-CCK'-CCZ
  hb1881 = ListNF.listnfeq' nf-e4 auto

  hb1882 : Goal L.ax-CCZ-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-CS12-CCZ
  hb1882 = ListNF.listnfeq' nf-e4 auto

  hb1883 : Goal L.ax-CCZ-CK10-CCK'=CK10-CCK'-CCZ
  hb1883 = ListNF.listnfeq' nf-e3 auto

  hb1884 : Goal L.ax-CCZ-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb1884 = ListNF.listnfeq' nf-e3 auto

  hb1885 : Goal L.ax-CCZ-CK20-S0-CK10=CK20-S0-CK10-CCX0-CS12-CCZ
  hb1885 = ListNF.listnfeq' nf-e3 auto

  hb1886 : Goal L.ax-CCZ-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CCX0
  hb1886 = ListNF.listnfeq' nf-e3 auto

  hb1887 : Goal L.ax-CCZ-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CCZ
  hb1887 = ListNF.listnfeq' nf-e3 auto

  hb1888 : Goal L.ax-CCZ-CK20-CK10=CK20-CK10-CCZ
  hb1888 = ListNF.listnfeq' nf-e3 auto

  hb1889 : Goal L.ax-CCZ-CK20-CK10-CCK'=CK20-CK10-CCK'-CCX0-CS12-CCZ
  hb1889 = ListNF.listnfeq' nf-e3 auto

  hb1890 : Goal L.ax-CCZ-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0
  hb1890 = ListNF.listnfeq' nf-e3 auto

  hb1891 : Goal L.ax-CCZ-CK20-CCK'=CK20-CCK'-CCZ
  hb1891 = ListNF.listnfeq' nf-e3 auto

  hb1892 : Goal L.ax-CCZ-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CCX0-CS12-CCZ
  hb1892 = ListNF.listnfeq' nf-e3 auto

  hb1893 : Goal L.ax-K0-S0-K0-S0-CK10=S0-K0-CK10-X0-CX10-CS01-CS01
  hb1893 = ListNF.listnfeq' nf-e4 auto

  hb1894 : Goal L.ax-K0-S0-K0-S0-CK10-CCK'=S0-K0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12
  hb1894 = ListNF.listnfeq' nf-e4 auto

  hb1895 : Goal L.ax-K0-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ
  hb1895 = ListNF.listnfeq' nf-e4 auto

  hb1896 : Goal L.ax-K0-S0-K0-S0-CK20=S0-K0-CK20-X0-CX20-CS02-CS02
  hb1896 = ListNF.listnfeq' nf-e4 auto

  hb1897 : Goal L.ax-K0-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI
  hb1897 = ListNF.listnfeq' nf-e4 auto

  hb1898 : Goal L.ax-K0-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI
  hb1898 = ListNF.listnfeq' nf-e4 auto

  hb1899 : Goal L.ax-K0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI
  hb1899 = ListNF.listnfeq' nf-e4 auto

  hb1900 : Goal L.ax-K0-S0-K0-S0-CK20-CK10=S0-K0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02
  hb1900 = ListNF.listnfeq' nf-e4 auto

  hb1901 : Goal L.ax-K0-S0-K0-S0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ
  hb1901 = ListNF.listnfeq' nf-e4 auto

  hb1902 : Goal L.ax-K0-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ
  hb1902 = ListNF.listnfeq' nf-e4 auto

  hb1903 : Goal L.ax-K0-S0-K0-S0-CK20-CCK'=S0-K0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12
  hb1903 = ListNF.listnfeq' nf-e4 auto

  hb1904 : Goal L.ax-K0-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ
  hb1904 = ListNF.listnfeq' nf-e4 auto

  hb1905 : Goal L.ax-K0-S0-K0-CK10=S0-K0-S0-CK10-X0-CX10-CS01-CS01-iI-iI-iI
  hb1905 = ListNF.listnfeq' nf-e4 auto

  hb1906 : Goal L.ax-K0-S0-K0-CK10-CCK'=S0-K0-S0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12-iI-iI-iI
  hb1906 = ListNF.listnfeq' nf-e4 auto

  hb1907 : Goal L.ax-K0-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ-iI-iI-iI
  hb1907 = ListNF.listnfeq' nf-e4 auto

  hb1908 : Goal L.ax-K0-S0-K0-CK20=S0-K0-S0-CK20-X0-CX20-CS02-CS02-iI-iI-iI
  hb1908 = ListNF.listnfeq' nf-e4 auto

  hb1909 : Goal L.ax-K0-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI
  hb1909 = ListNF.listnfeq' nf-e4 auto

  hb1910 : Goal L.ax-K0-S0-K0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI
  hb1910 = ListNF.listnfeq' nf-e4 auto

  hb1911 : Goal L.ax-K0-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI
  hb1911 = ListNF.listnfeq' nf-e4 auto

  hb1912 : Goal L.ax-K0-S0-K0-CK20-CK10=S0-K0-S0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02-iI-iI-iI
  hb1912 = ListNF.listnfeq' nf-e4 auto

  hb1913 : Goal L.ax-K0-S0-K0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ-iI-iI-iI
  hb1913 = ListNF.listnfeq' nf-e4 auto

  hb1914 : Goal L.ax-K0-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ-iI-iI-iI
  hb1914 = ListNF.listnfeq' nf-e4 auto

  hb1915 : Goal L.ax-K0-S0-K0-CK20-CCK'=S0-K0-S0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12-iI-iI-iI
  hb1915 = ListNF.listnfeq' nf-e4 auto

  hb1916 : Goal L.ax-K0-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ-iI-iI-iI
  hb1916 = ListNF.listnfeq' nf-e4 auto

  hb1917 : Goal L.ax-K0-S0-K0-CCK'=S0-K0-CCK'-CCK'-X0-CCX0-S0-S0-S0-CCZ
  hb1917 = ListNF.listnfeq' nf-e4 auto

  hb1918 : Goal L.ax-K0-S0-K0-CCK'-CCK'=S0-K0-CCK'-X0-CCX0-S0-S0-S0-CS12-CS12-CS12
  hb1918 = ListNF.listnfeq' nf-e4 auto

  hb1919 : Goal L.ax-K0-K0-S0-CK10=S0-CK10-iI-iI-iI
  hb1919 = ListNF.listnfeq' nf-e4 auto

  hb1920 : Goal L.ax-K0-K0-S0-CK10-CCK'=S0-CK10-CCK'-iI-iI-iI
  hb1920 = ListNF.listnfeq' nf-e4 auto

  hb1921 : Goal L.ax-K0-K0-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-iI-iI-iI
  hb1921 = ListNF.listnfeq' nf-e4 auto

  hb1922 : Goal L.ax-K0-K0-S0-CK20=S0-CK20-iI-iI-iI
  hb1922 = ListNF.listnfeq' nf-e4 auto

  hb1923 : Goal L.ax-K0-K0-S0-CK20-S0-CK10=S0-CK20-S0-CK10-iI-iI-iI
  hb1923 = ListNF.listnfeq' nf-e4 auto

  hb1924 : Goal L.ax-K0-K0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-iI-iI-iI
  hb1924 = ListNF.listnfeq' nf-e4 auto

  hb1925 : Goal L.ax-K0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-iI-iI-iI
  hb1925 = ListNF.listnfeq' nf-e4 auto

  hb1926 : Goal L.ax-K0-K0-S0-CK20-CK10=S0-CK20-CK10-iI-iI-iI
  hb1926 = ListNF.listnfeq' nf-e4 auto

  hb1927 : Goal L.ax-K0-K0-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-iI-iI-iI
  hb1927 = ListNF.listnfeq' nf-e4 auto

  hb1928 : Goal L.ax-K0-K0-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-iI-iI-iI
  hb1928 = ListNF.listnfeq' nf-e4 auto

  hb1929 : Goal L.ax-K0-K0-S0-CK20-CCK'=S0-CK20-CCK'-iI-iI-iI
  hb1929 = ListNF.listnfeq' nf-e4 auto

  hb1930 : Goal L.ax-K0-K0-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-iI-iI-iI
  hb1930 = ListNF.listnfeq' nf-e4 auto

  hb1931 : Goal L.ax-K0-K0-CK10=CK10-iI-iI-iI
  hb1931 = ListNF.listnfeq' nf-e4 auto

  hb1932 : Goal L.ax-K0-K0-CK10-CCK'=CK10-CCK'-iI-iI-iI
  hb1932 = ListNF.listnfeq' nf-e4 auto

  hb1933 : Goal L.ax-K0-K0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-iI-iI-iI
  hb1933 = ListNF.listnfeq' nf-e4 auto

  hb1934 : Goal L.ax-K0-K0-CK20=CK20-iI-iI-iI
  hb1934 = ListNF.listnfeq' nf-e4 auto

  hb1935 : Goal L.ax-K0-K0-CK20-S0-CK10=CK20-S0-CK10-iI-iI-iI
  hb1935 = ListNF.listnfeq' nf-e4 auto

  hb1936 : Goal L.ax-K0-K0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-iI-iI-iI
  hb1936 = ListNF.listnfeq' nf-e4 auto

  hb1937 : Goal L.ax-K0-K0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-iI-iI-iI
  hb1937 = ListNF.listnfeq' nf-e4 auto

  hb1938 : Goal L.ax-K0-K0-CK20-CK10=CK20-CK10-iI-iI-iI
  hb1938 = ListNF.listnfeq' nf-e4 auto

  hb1939 : Goal L.ax-K0-K0-CK20-CK10-CCK'=CK20-CK10-CCK'-iI-iI-iI
  hb1939 = ListNF.listnfeq' nf-e4 auto

  hb1940 : Goal L.ax-K0-K0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-iI-iI-iI
  hb1940 = ListNF.listnfeq' nf-e4 auto

  hb1941 : Goal L.ax-K0-K0-CK20-CCK'=CK20-CCK'-iI-iI-iI
  hb1941 = ListNF.listnfeq' nf-e4 auto

  hb1942 : Goal L.ax-K0-K0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-iI-iI-iI
  hb1942 = ListNF.listnfeq' nf-e4 auto

  hb1943 : Goal L.ax-K0-K0-CCK'=CCK'-iI-iI-iI
  hb1943 = ListNF.listnfeq' nf-e4 auto

  hb1944 : Goal L.ax-K0-K0-CCK'-CCK'=CCK'-CCK'-iI-iI-iI
  hb1944 = ListNF.listnfeq' nf-e4 auto

  hb1945 : Goal L.ax-X0-S0-K0-S0-CK10=S0-K0-S0-CK10-X0-CX10-CS01-CS01
  hb1945 = ListNF.listnfeq' nf-e4 auto

  hb1946 : Goal L.ax-X0-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12
  hb1946 = ListNF.listnfeq' nf-e4 auto

  hb1947 : Goal L.ax-X0-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ
  hb1947 = ListNF.listnfeq' nf-e4 auto

  hb1948 : Goal L.ax-X0-S0-K0-S0-CK20=S0-K0-S0-CK20-X0-CX20-CS02-CS02
  hb1948 = ListNF.listnfeq' nf-e4 auto

  hb1949 : Goal L.ax-X0-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI
  hb1949 = ListNF.listnfeq' nf-e4 auto

  hb1950 : Goal L.ax-X0-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI
  hb1950 = ListNF.listnfeq' nf-e4 auto

  hb1951 : Goal L.ax-X0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI
  hb1951 = ListNF.listnfeq' nf-e4 auto

  hb1952 : Goal L.ax-X0-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02
  hb1952 = ListNF.listnfeq' nf-e4 auto

  hb1953 : Goal L.ax-X0-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ
  hb1953 = ListNF.listnfeq' nf-e4 auto

  hb1954 : Goal L.ax-X0-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ
  hb1954 = ListNF.listnfeq' nf-e4 auto

  hb1955 : Goal L.ax-X0-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12
  hb1955 = ListNF.listnfeq' nf-e4 auto

  hb1956 : Goal L.ax-X0-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ
  hb1956 = ListNF.listnfeq' nf-e4 auto

  hb1957 : Goal L.ax-X0-S0-K0-CK10=S0-K0-CK10-X0-S0-S0-S1-S1-iI
  hb1957 = ListNF.listnfeq' nf-e4 auto

  hb1958 : Goal L.ax-X0-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-X0-S0-S0-S1-S1-CS12-CS12-CS12-CCZ-iI
  hb1958 = ListNF.listnfeq' nf-e4 auto

  hb1959 : Goal L.ax-X0-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-CS12-CS12-CS12-iI
  hb1959 = ListNF.listnfeq' nf-e4 auto

  hb1960 : Goal L.ax-X0-S0-K0-CK20=S0-K0-CK20-X0-S0-S0-S2-S2-iI
  hb1960 = ListNF.listnfeq' nf-e4 auto

  hb1961 : Goal L.ax-X0-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-X0-CX10-S2-S2-CS01-CS01
  hb1961 = ListNF.listnfeq' nf-e4 auto

  hb1962 : Goal L.ax-X0-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CS12
  hb1962 = ListNF.listnfeq' nf-e4 auto

  hb1963 : Goal L.ax-X0-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CCZ
  hb1963 = ListNF.listnfeq' nf-e4 auto

  hb1964 : Goal L.ax-X0-S0-K0-CK20-CK10=S0-K0-CK20-CK10-X0-S0-S0-S1-S1-S2-S2-iI
  hb1964 = ListNF.listnfeq' nf-e4 auto

  hb1965 : Goal L.ax-X0-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-X0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-CCZ-iI
  hb1965 = ListNF.listnfeq' nf-e4 auto

  hb1966 : Goal L.ax-X0-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-iI
  hb1966 = ListNF.listnfeq' nf-e4 auto

  hb1967 : Goal L.ax-X0-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-X0-S0-S0-S2-S2-CS12-CS12-CS12-CCZ-iI
  hb1967 = ListNF.listnfeq' nf-e4 auto

  hb1968 : Goal L.ax-X0-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-X0-CCX0-S0-S0-S2-S2-CS12-CS12-CS12-iI
  hb1968 = ListNF.listnfeq' nf-e4 auto

  hb1969 : Goal L.ax-X0-S0-K0-CCK'=S0-K0-CCK'-X0-S0-S0-CS12-CS12-CS12-CCZ-iI
  hb1969 = ListNF.listnfeq' nf-e4 auto

  hb1970 : Goal L.ax-X0-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-X0-CCX0-S0-S0-CS12-CS12-CS12-iI
  hb1970 = ListNF.listnfeq' nf-e4 auto

  hb1971 : Goal L.ax-X0-S0-CK10-CCK'=S0-CK10-CCK'-X0-S0-S0-S1-S1-CS12-CS12-CS12-CCZ-iI-iI-iI
  hb1971 = ListNF.listnfeq' nf-e3 auto

  hb1972 : Goal L.ax-X0-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-CS12-CS12-CS12-iI-iI-iI
  hb1972 = ListNF.listnfeq' nf-e3 auto

  hb1973 : Goal L.ax-X0-S0-CK20-S0-CK10=S0-CK20-S0-CK10-X0-CX10-S2-S2-CS01-CS01-iI-iI
  hb1973 = ListNF.listnfeq' nf-e3 auto

  hb1974 : Goal L.ax-X0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CS12-iI-iI
  hb1974 = ListNF.listnfeq' nf-e3 auto

  hb1975 : Goal L.ax-X0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CCZ-iI-iI
  hb1975 = ListNF.listnfeq' nf-e3 auto

  hb1976 : Goal L.ax-X0-S0-CK20-CK10=S0-CK20-CK10-X0-S0-S0-S1-S1-S2-S2-iI-iI-iI
  hb1976 = ListNF.listnfeq' nf-e3 auto

  hb1977 : Goal L.ax-X0-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-X0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI
  hb1977 = ListNF.listnfeq' nf-e3 auto

  hb1978 : Goal L.ax-X0-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-iI-iI-iI
  hb1978 = ListNF.listnfeq' nf-e3 auto

  hb1979 : Goal L.ax-X0-S0-CK20-CCK'=S0-CK20-CCK'-X0-S0-S0-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI
  hb1979 = ListNF.listnfeq' nf-e3 auto

  hb1980 : Goal L.ax-X0-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-X0-CCX0-S0-S0-S2-S2-CS12-CS12-CS12-iI-iI-iI
  hb1980 = ListNF.listnfeq' nf-e3 auto

  hb1981 : Goal L.ax-X0-K0-S0-CK10=K0-S0-CK10-CX10-S0-S0-CS01-CS01
  hb1981 = ListNF.listnfeq' nf-e4 auto

  hb1982 : Goal L.ax-X0-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CCZ
  hb1982 = ListNF.listnfeq' nf-e4 auto

  hb1983 : Goal L.ax-X0-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-S0-S0-CS01-CS01-CS12-CCZ
  hb1983 = ListNF.listnfeq' nf-e4 auto

  hb1984 : Goal L.ax-X0-K0-S0-CK20=K0-S0-CK20-CX20-S0-S0-CS02-CS02
  hb1984 = ListNF.listnfeq' nf-e4 auto

  hb1985 : Goal L.ax-X0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ
  hb1985 = ListNF.listnfeq' nf-e4 auto

  hb1986 : Goal L.ax-X0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12
  hb1986 = ListNF.listnfeq' nf-e4 auto

  hb1987 : Goal L.ax-X0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS12-CCZ
  hb1987 = ListNF.listnfeq' nf-e4 auto

  hb1988 : Goal L.ax-X0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02
  hb1988 = ListNF.listnfeq' nf-e4 auto

  hb1989 : Goal L.ax-X0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12
  hb1989 = ListNF.listnfeq' nf-e4 auto

  hb1990 : Goal L.ax-X0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb1990 = ListNF.listnfeq' nf-e4 auto

  hb1991 : Goal L.ax-X0-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-S0-S0-CS02-CS02-CCZ
  hb1991 = ListNF.listnfeq' nf-e4 auto

  hb1992 : Goal L.ax-X0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-S0-S0-CS02-CS02-CS12-CCZ
  hb1992 = ListNF.listnfeq' nf-e4 auto

  hb1993 : Goal L.ax-X0-K0-CK10=K0-CK10-CX10-S0-S0-CS01-CS01
  hb1993 = ListNF.listnfeq' nf-e4 auto

  hb1994 : Goal L.ax-X0-K0-CK10-CCK'=K0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CCZ
  hb1994 = ListNF.listnfeq' nf-e4 auto

  hb1995 : Goal L.ax-X0-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX10-S0-S0-CS01-CS01-CS12-CCZ
  hb1995 = ListNF.listnfeq' nf-e4 auto

  hb1996 : Goal L.ax-X0-K0-CK20=K0-CK20-CX20-S0-S0-CS02-CS02
  hb1996 = ListNF.listnfeq' nf-e4 auto

  hb1997 : Goal L.ax-X0-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ
  hb1997 = ListNF.listnfeq' nf-e4 auto

  hb1998 : Goal L.ax-X0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12
  hb1998 = ListNF.listnfeq' nf-e4 auto

  hb1999 : Goal L.ax-X0-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS12-CCZ
  hb1999 = ListNF.listnfeq' nf-e4 auto

  hb2000 : Goal L.ax-X0-K0-CK20-CK10=K0-CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02
  hb2000 = ListNF.listnfeq' nf-e4 auto

  hb2001 : Goal L.ax-X0-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12
  hb2001 = ListNF.listnfeq' nf-e4 auto

  hb2002 : Goal L.ax-X0-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ
  hb2002 = ListNF.listnfeq' nf-e4 auto

  hb2003 : Goal L.ax-X0-K0-CK20-CCK'=K0-CK20-CCK'-CX20-CCX0-S0-S0-CS02-CS02-CCZ
  hb2003 = ListNF.listnfeq' nf-e4 auto

  hb2004 : Goal L.ax-X0-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX20-S0-S0-CS02-CS02-CS12-CCZ
  hb2004 = ListNF.listnfeq' nf-e4 auto

  hb2005 : Goal L.ax-X0-K0-CCK'=K0-CCK'-CCX0-S0-S0-CS12
  hb2005 = ListNF.listnfeq' nf-e4 auto

  hb2006 : Goal L.ax-X0-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-S0-S0-CCZ
  hb2006 = ListNF.listnfeq' nf-e4 auto

  hb2007 : Goal L.ax-X0-CK10-CCK'=CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12
  hb2007 = ListNF.listnfeq' nf-e3 auto

  hb2008 : Goal L.ax-X0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ
  hb2008 = ListNF.listnfeq' nf-e3 auto

  hb2009 : Goal L.ax-X0-CK20-S0-CK10=CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI
  hb2009 = ListNF.listnfeq' nf-e3 auto

  hb2010 : Goal L.ax-X0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI
  hb2010 = ListNF.listnfeq' nf-e3 auto

  hb2011 : Goal L.ax-X0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI
  hb2011 = ListNF.listnfeq' nf-e3 auto

  hb2012 : Goal L.ax-X0-CK20-CK10=CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02
  hb2012 = ListNF.listnfeq' nf-e3 auto

  hb2013 : Goal L.ax-X0-CK20-CK10-CCK'=CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ
  hb2013 = ListNF.listnfeq' nf-e3 auto

  hb2014 : Goal L.ax-X0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ
  hb2014 = ListNF.listnfeq' nf-e3 auto

  hb2015 : Goal L.ax-X0-CK20-CCK'=CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12
  hb2015 = ListNF.listnfeq' nf-e3 auto

  hb2016 : Goal L.ax-X0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ
  hb2016 = ListNF.listnfeq' nf-e3 auto

  hb2017 : Goal L.ax-X1-S0-K0=S0-K0-X1
  hb2017 = ListNF.listnfeq' nf-p24k0d auto

  hb2018 : Goal L.ax-X1-S0-K0-S0-CK10=K0-S0-CK10-X1-X0-CX10-S1-S1-S1-CS01-CS01-iI
  hb2018 = ListNF.listnfeq' nf-p24k0d auto

  hb2019 : Goal L.ax-X1-S0-K0-S0-CK10-CCK'=K0-S0-CK20-CK10-CCK'-X1-X0-CX10-CCX0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CCZ-iI
  hb2019 = ListNF.listnfeq' nf-p24k0d auto

  hb2020 : Goal L.ax-X1-S0-K0-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12-iI
  hb2020 = ListNF.listnfeq' nf-p24k0d auto

  hb2021 : Goal L.ax-X1-S0-K0-S0-CK20=S0-K0-S0-CK20-X1
  hb2021 = ListNF.listnfeq' nf-p24k0d auto

  hb2022 : Goal L.ax-X1-S0-K0-S0-CK20-S0-CK10=S0-CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12
  hb2022 = ListNF.listnfeq' nf-p24k0d auto

  hb2023 : Goal L.ax-X1-S0-K0-S0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS12-CS12-CS12
  hb2023 = ListNF.listnfeq' nf-p24k0d auto

  hb2024 : Goal L.ax-X1-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ
  hb2024 = ListNF.listnfeq' nf-p24k0d auto

  hb2025 : Goal L.ax-X1-S0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-X1-X0-CX10-CX20-S1-S1-S1-CS01-CS01-CS02-CS02-iI
  hb2025 = ListNF.listnfeq' nf-p24k0d auto

  hb2026 : Goal L.ax-X1-S0-K0-S0-CK20-CK10-CCK'=K0-S0-CK10-CCK'-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-iI
  hb2026 = ListNF.listnfeq' nf-p24k0d auto

  hb2027 : Goal L.ax-X1-S0-K0-S0-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ-iI
  hb2027 = ListNF.listnfeq' nf-p24k0d auto

  hb2028 : Goal L.ax-X1-S0-K0-S0-CK20-CCK'=S0-K0-CCK'-CCK'-X1-S0-S2-CS02-CS02-CS02-CS12-CS12
  hb2028 = ListNF.listnfeq' nf-p24k0d auto

  hb2029 : Goal L.ax-X1-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-X1-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12
  hb2029 = ListNF.listnfeq' nf-p24k0d auto

  hb2030 : Goal L.ax-X1-S0-K0-CK10=S0-CK10-X1-S1-S1-S1
  hb2030 = ListNF.listnfeq' nf-p24k0d auto

  hb2031 : Goal L.ax-X1-S0-K0-CK10-CCK'=S0-CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ
  hb2031 = ListNF.listnfeq' nf-p24k0d auto

  hb2032 : Goal L.ax-X1-S0-K0-CK10-CCK'-CCK'=CK20-S0-CK10-X1-CX20-S1-S1-S1-S2-CS02-CS02-CS02-CS12-CCZ
  hb2032 = ListNF.listnfeq' nf-p24k0d auto

  hb2033 : Goal L.ax-X1-S0-K0-CK20=S0-K0-CK20-X1
  hb2033 = ListNF.listnfeq' nf-p24k0d auto

  hb2034 : Goal L.ax-X1-S0-K0-CK20-S0-CK10=K0-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-iI
  hb2034 = ListNF.listnfeq' nf-p24k0d auto

  hb2035 : Goal L.ax-X1-S0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS02-CS12-CS12-CS12-iI
  hb2035 = ListNF.listnfeq' nf-p24k0d auto

  hb2036 : Goal L.ax-X1-S0-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-X1-X0-CX10-CCX0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS12-CS12-CCZ-iI
  hb2036 = ListNF.listnfeq' nf-p24k0d auto

  hb2037 : Goal L.ax-X1-S0-K0-CK20-CK10=S0-CK20-CK10-X1-S1-S1-S1
  hb2037 = ListNF.listnfeq' nf-p24k0d auto

  hb2038 : Goal L.ax-X1-S0-K0-CK20-CK10-CCK'=S0-CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ
  hb2038 = ListNF.listnfeq' nf-p24k0d auto

  hb2039 : Goal L.ax-X1-S0-K0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-X1-S1-S1-S1-S2-CS02-CS02-CS12-CS12
  hb2039 = ListNF.listnfeq' nf-p24k0d auto

  hb2040 : Goal L.ax-X1-S0-K0-CK20-CCK'=S0-K0-CCK'-X1-CS02-CS12-CS12-CS12-CCZ
  hb2040 = ListNF.listnfeq' nf-p24k0d auto

  hb2041 : Goal L.ax-X1-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X1-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ
  hb2041 = ListNF.listnfeq' nf-p24k0d auto

  hb2042 : Goal L.ax-X1-S0-K0-CCK'=S0-K0-CK20-CCK'-X1-S2-CS02-CS12-CS12-CS12-CCZ
  hb2042 = ListNF.listnfeq' nf-p24k0d auto

  hb2043 : Goal L.ax-X1-S0-K0-CCK'-CCK'=S0-K0-S0-CK20-CCK'-X1-S0-S0-S0-S2-CS02-CS12-CS12
  hb2043 = ListNF.listnfeq' nf-p24k0d auto

  hb2044 : Goal L.ax-X1-S0-CK10=S0-K0-CK10-X1-S1-S1-S1-iI
  hb2044 = ListNF.listnfeq' nf-p24k0d auto

  hb2045 : Goal L.ax-X1-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ-iI
  hb2045 = ListNF.listnfeq' nf-p24k0d auto

  hb2046 : Goal L.ax-X1-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12-iI
  hb2046 = ListNF.listnfeq' nf-p24k0d auto

  hb2047 : Goal L.ax-X1-S0-CK20=S0-CK20-X1
  hb2047 = ListNF.listnfeq' nf-p24k0d auto

  hb2048 : Goal L.ax-X1-S0-CK20-S0-CK10=K0-CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-iI
  hb2048 = ListNF.listnfeq' nf-p24k0d auto

  hb2049 : Goal L.ax-X1-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-X1-X0-S0-S0-S1-S2-CS02-CS02-iI
  hb2049 = ListNF.listnfeq' nf-p24k0d auto

  hb2050 : Goal L.ax-X1-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ-iI
  hb2050 = ListNF.listnfeq' nf-p24k0d auto

  hb2051 : Goal L.ax-X1-S0-CK20-CK10=S0-K0-CK20-CK10-X1-S1-S1-S1-iI
  hb2051 = ListNF.listnfeq' nf-p24k0d auto

  hb2052 : Goal L.ax-X1-S0-CK20-CK10-CCK'=S0-K0-CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ-iI
  hb2052 = ListNF.listnfeq' nf-p24k0d auto

  hb2053 : Goal L.ax-X1-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ-iI
  hb2053 = ListNF.listnfeq' nf-p24k0d auto

  hb2054 : Goal L.ax-X1-S0-CK20-CCK'=CCK'-CCK'-X1-S0-S2-CS02-CS02-CS02-CS12-CS12
  hb2054 = ListNF.listnfeq' nf-p24k0d auto

  hb2055 : Goal L.ax-X1-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-X1-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12
  hb2055 = ListNF.listnfeq' nf-p24k0d auto

  hb2056 : Goal L.ax-X1-K0-S0-CK10=S0-K0-S0-CK10-X1-CX10-S0-S0-S1-S1-S1-CS01-CS01
  hb2056 = ListNF.listnfeq' nf-p24k0d auto

  hb2057 : Goal L.ax-X1-K0-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS12-CS12-CS12
  hb2057 = ListNF.listnfeq' nf-p24k0d auto

  hb2058 : Goal L.ax-X1-K0-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ
  hb2058 = ListNF.listnfeq' nf-p24k0d auto

  hb2059 : Goal L.ax-X1-K0-S0-CK20=K0-S0-CK20-X1
  hb2059 = ListNF.listnfeq' nf-p24k0d auto

  hb2060 : Goal L.ax-X1-K0-S0-CK20-S0-CK10=CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12
  hb2060 = ListNF.listnfeq' nf-p24k0d auto

  hb2061 : Goal L.ax-X1-K0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-X1-X0-S0-S0-S1-S2-CS02-CS02
  hb2061 = ListNF.listnfeq' nf-p24k0d auto

  hb2062 : Goal L.ax-X1-K0-S0-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ
  hb2062 = ListNF.listnfeq' nf-p24k0d auto

  hb2063 : Goal L.ax-X1-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-X1-CX10-CX20-S0-S0-S1-S1-S1-CS01-CS01-CS02-CS02
  hb2063 = ListNF.listnfeq' nf-p24k0d auto

  hb2064 : Goal L.ax-X1-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK10-CCK'-X1-CX10-CX20-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS12-CS12-CCZ
  hb2064 = ListNF.listnfeq' nf-p24k0d auto

  hb2065 : Goal L.ax-X1-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X1-CX10-CX20-CCX0-S0-S0-S1-S1-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ
  hb2065 = ListNF.listnfeq' nf-p24k0d auto

  hb2066 : Goal L.ax-X1-K0-S0-CK20-CCK'=K0-CCK'-CCK'-X1-S0-S2-CS02-CS02-CS02-CS12-CS12
  hb2066 = ListNF.listnfeq' nf-p24k0d auto

  hb2067 : Goal L.ax-X1-K0-S0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-X1-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12
  hb2067 = ListNF.listnfeq' nf-p24k0d auto

  hb2068 : Goal L.ax-X1-K0-CK10=CK10-X1-S1-S1-S1
  hb2068 = ListNF.listnfeq' nf-p24k0d auto

  hb2069 : Goal L.ax-X1-K0-CK10-CCK'=CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ
  hb2069 = ListNF.listnfeq' nf-p24k0d auto

  hb2070 : Goal L.ax-X1-K0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12
  hb2070 = ListNF.listnfeq' nf-p24k0d auto

  hb2071 : Goal L.ax-X1-K0-CK20=K0-CK20-X1
  hb2071 = ListNF.listnfeq' nf-p24k0d auto

  hb2072 : Goal L.ax-X1-K0-CK20-S0-CK10=S0-K0-S0-CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12
  hb2072 = ListNF.listnfeq' nf-p24k0d auto

  hb2073 : Goal L.ax-X1-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS12-CS12-CS12
  hb2073 = ListNF.listnfeq' nf-p24k0d auto

  hb2074 : Goal L.ax-X1-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ
  hb2074 = ListNF.listnfeq' nf-p24k0d auto

  hb2075 : Goal L.ax-X1-K0-CK20-CK10=CK20-CK10-X1-S1-S1-S1
  hb2075 = ListNF.listnfeq' nf-p24k0d auto

  hb2076 : Goal L.ax-X1-K0-CK20-CK10-CCK'=CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ
  hb2076 = ListNF.listnfeq' nf-p24k0d auto

  hb2077 : Goal L.ax-X1-K0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ
  hb2077 = ListNF.listnfeq' nf-p24k0d auto

  hb2078 : Goal L.ax-X1-K0-CK20-CCK'=K0-CCK'-X1-CS02-CS12-CS12-CS12-CCZ
  hb2078 = ListNF.listnfeq' nf-p24k0d auto

  hb2079 : Goal L.ax-X1-K0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-X1-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ
  hb2079 = ListNF.listnfeq' nf-p24k0d auto

  hb2080 : Goal L.ax-X1-K0-CCK'=K0-CK20-CCK'-X1-S2-CS02-CS12-CS12-CS12-CCZ
  hb2080 = ListNF.listnfeq' nf-p24k0d auto

  hb2081 : Goal L.ax-X1-K0-CCK'-CCK'=K0-S0-CK20-CCK'-X1-S0-S0-S0-S2-CS02-CS12-CS12
  hb2081 = ListNF.listnfeq' nf-p24k0d auto

  hb2082 : Goal L.ax-X1-CK10=K0-CK10-X1-S1-S1-S1-iI
  hb2082 = ListNF.listnfeq' nf-p24k0d auto

  hb2083 : Goal L.ax-X1-CK10-CCK'=K0-CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ-iI
  hb2083 = ListNF.listnfeq' nf-p24k0d auto

  hb2084 : Goal L.ax-X1-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12-iI
  hb2084 = ListNF.listnfeq' nf-p24k0d auto

  hb2085 : Goal L.ax-X1-CK20-S0-CK10=S0-K0-CK10-CCK'-CCK'-X1-CX20-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ-iI
  hb2085 = ListNF.listnfeq' nf-p24k0d auto

  hb2086 : Goal L.ax-X1-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS02-CS12-CS12-CS12-iI
  hb2086 = ListNF.listnfeq' nf-p24k0d auto

  hb2087 : Goal L.ax-X1-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X1-S1-S1-S1-S2-CS02-CS02-CS12-CS12-iI
  hb2087 = ListNF.listnfeq' nf-p24k0d auto

  hb2088 : Goal L.ax-X1-CK20-CK10=K0-CK20-CK10-X1-S1-S1-S1-iI
  hb2088 = ListNF.listnfeq' nf-p24k0d auto

  hb2089 : Goal L.ax-X1-CK20-CK10-CCK'=K0-CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ-iI
  hb2089 = ListNF.listnfeq' nf-p24k0d auto

  hb2090 : Goal L.ax-X1-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ-iI
  hb2090 = ListNF.listnfeq' nf-p24k0d auto

  hb2091 : Goal L.ax-X1-CK20-CCK'=CCK'-X1-CS02-CS12-CS12-CS12-CCZ
  hb2091 = ListNF.listnfeq' nf-p24k0d auto

  hb2092 : Goal L.ax-X1-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-X1-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ
  hb2092 = ListNF.listnfeq' nf-p24k0d auto

  hb2093 : Goal L.ax-X1-CCK'=CK20-CCK'-X1-S2-CS02-CS12-CS12-CS12-CCZ
  hb2093 = ListNF.listnfeq' nf-p24k0d auto

  hb2094 : Goal L.ax-X1-CCK'-CCK'=S0-CK20-CCK'-X1-S0-S0-S0-S2-CS02-CS12-CS12
  hb2094 = ListNF.listnfeq' nf-p24k0d auto

  hb2095 : Goal L.ax-X2-S0-K0=S0-K0-X2
  hb2095 = ListNF.listnfeq' nf-p24k0d auto

  hb2096 : Goal L.ax-X2-S0-K0-S0-CK10=S0-K0-S0-CK10-X2
  hb2096 = ListNF.listnfeq' nf-p24k0d auto

  hb2097 : Goal L.ax-X2-S0-K0-S0-CK10-CCK'=S0-K0-CCK'-CCK'-X2-S0-S1-CS01-CS01-CS01-CS12-CS12
  hb2097 = ListNF.listnfeq' nf-p24k0d auto

  hb2098 : Goal L.ax-X2-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12
  hb2098 = ListNF.listnfeq' nf-p24k0d auto

  hb2099 : Goal L.ax-X2-S0-K0-S0-CK20=K0-S0-CK20-X2-X0-CX20-S2-S2-S2-CS02-CS02-iI
  hb2099 = ListNF.listnfeq' nf-p24k0d auto

  hb2100 : Goal L.ax-X2-S0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-X2-X0-CX20-CCX0-S0-S0-S1-S1-CS12-CS12-CCZ
  hb2100 = ListNF.listnfeq' nf-p24k0d auto

  hb2101 : Goal L.ax-X2-S0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-CCK'-CCK'-X2-X0-CX20-S0-S1-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CCZ-iI
  hb2101 = ListNF.listnfeq' nf-p24k0d auto

  hb2102 : Goal L.ax-X2-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-X2-X0-CX10-CX20-S0-S1-S1-S2-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ-iI
  hb2102 = ListNF.listnfeq' nf-p24k0d auto

  hb2103 : Goal L.ax-X2-S0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-X2-X0-CX10-CX20-S2-S2-S2-CS01-CS01-CS02-CS02-iI
  hb2103 = ListNF.listnfeq' nf-p24k0d auto

  hb2104 : Goal L.ax-X2-S0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CCK'-X2-X0-CX10-CX20-CCX0-S2-S2-S2-CS01-CS01-CS01-CS02-CS02-CS12-CS12-CS12-iI
  hb2104 = ListNF.listnfeq' nf-p24k0d auto

  hb2105 : Goal L.ax-X2-S0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-X2-X0-CX10-CX20-CCX0-S0-S1-S1-CS01-CS01-CS12
  hb2105 = ListNF.listnfeq' nf-p24k0d auto

  hb2106 : Goal L.ax-X2-S0-K0-S0-CK20-CCK'=K0-S0-CK20-CK10-CCK'-X2-X0-CX20-CCX0-S1-S1-S2-S2-S2-CS01-CS01-CS01-CS02-CS02-CS12-CS12-CCZ-iI
  hb2106 = ListNF.listnfeq' nf-p24k0d auto

  hb2107 : Goal L.ax-X2-S0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-X2-X0-CX20-CCX0-S0-S1-S1-CS01-CS01-CS01-CS12
  hb2107 = ListNF.listnfeq' nf-p24k0d auto

  hb2108 : Goal L.ax-X2-S0-K0-CK10=S0-K0-CK10-X2
  hb2108 = ListNF.listnfeq' nf-p24k0d auto

  hb2109 : Goal L.ax-X2-S0-K0-CK10-CCK'=S0-K0-CCK'-X2-CS01-CS12-CS12-CS12-CCZ
  hb2109 = ListNF.listnfeq' nf-p24k0d auto

  hb2110 : Goal L.ax-X2-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ
  hb2110 = ListNF.listnfeq' nf-p24k0d auto

  hb2111 : Goal L.ax-X2-S0-K0-CK20=S0-CK20-X2-S2-S2-S2
  hb2111 = ListNF.listnfeq' nf-p24k0d auto

  hb2112 : Goal L.ax-X2-S0-K0-CK20-S0-CK10=S0-CK20-S0-CK10-X2-S2-S2-S2
  hb2112 = ListNF.listnfeq' nf-p24k0d auto

  hb2113 : Goal L.ax-X2-S0-K0-CK20-S0-CK10-CCK'=S0-CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12
  hb2113 = ListNF.listnfeq' nf-p24k0d auto

  hb2114 : Goal L.ax-X2-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12
  hb2114 = ListNF.listnfeq' nf-p24k0d auto

  hb2115 : Goal L.ax-X2-S0-K0-CK20-CK10=S0-CK20-CK10-X2-S2-S2-S2
  hb2115 = ListNF.listnfeq' nf-p24k0d auto

  hb2116 : Goal L.ax-X2-S0-K0-CK20-CK10-CCK'=S0-CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ
  hb2116 = ListNF.listnfeq' nf-p24k0d auto

  hb2117 : Goal L.ax-X2-S0-K0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ
  hb2117 = ListNF.listnfeq' nf-p24k0d auto

  hb2118 : Goal L.ax-X2-S0-K0-CK20-CCK'=S0-CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ
  hb2118 = ListNF.listnfeq' nf-p24k0d auto

  hb2119 : Goal L.ax-X2-S0-K0-CK20-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12
  hb2119 = ListNF.listnfeq' nf-p24k0d auto

  hb2120 : Goal L.ax-X2-S0-K0-CCK'=S0-K0-CK10-CCK'-X2-S1-CS01-CS12-CS12-CS12-CCZ
  hb2120 = ListNF.listnfeq' nf-p24k0d auto

  hb2121 : Goal L.ax-X2-S0-K0-CCK'-CCK'=S0-K0-S0-CK10-CCK'-X2-S0-S0-S0-S1-CS01-CS12-CS12
  hb2121 = ListNF.listnfeq' nf-p24k0d auto

  hb2122 : Goal L.ax-X2-S0-CK10=S0-CK10-X2
  hb2122 = ListNF.listnfeq' nf-p24k0d auto

  hb2123 : Goal L.ax-X2-S0-CK10-CCK'=CCK'-CCK'-X2-S0-S1-CS01-CS01-CS01-CS12-CS12
  hb2123 = ListNF.listnfeq' nf-p24k0d auto

  hb2124 : Goal L.ax-X2-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12
  hb2124 = ListNF.listnfeq' nf-p24k0d auto

  hb2125 : Goal L.ax-X2-S0-CK20=S0-K0-CK20-X2-S2-S2-S2-iI
  hb2125 = ListNF.listnfeq' nf-p24k0d auto

  hb2126 : Goal L.ax-X2-S0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-X2-S2-S2-S2-iI
  hb2126 = ListNF.listnfeq' nf-p24k0d auto

  hb2127 : Goal L.ax-X2-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12-iI
  hb2127 = ListNF.listnfeq' nf-p24k0d auto

  hb2128 : Goal L.ax-X2-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12-iI
  hb2128 = ListNF.listnfeq' nf-p24k0d auto

  hb2129 : Goal L.ax-X2-S0-CK20-CK10=S0-K0-CK20-CK10-X2-S2-S2-S2-iI
  hb2129 = ListNF.listnfeq' nf-p24k0d auto

  hb2130 : Goal L.ax-X2-S0-CK20-CK10-CCK'=S0-K0-CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI
  hb2130 = ListNF.listnfeq' nf-p24k0d auto

  hb2131 : Goal L.ax-X2-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ-iI
  hb2131 = ListNF.listnfeq' nf-p24k0d auto

  hb2132 : Goal L.ax-X2-S0-CK20-CCK'=S0-K0-CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI
  hb2132 = ListNF.listnfeq' nf-p24k0d auto

  hb2133 : Goal L.ax-X2-S0-CK20-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12-iI
  hb2133 = ListNF.listnfeq' nf-p24k0d auto

  hb2134 : Goal L.ax-X2-K0-S0-CK10=K0-S0-CK10-X2
  hb2134 = ListNF.listnfeq' nf-p24k0d auto

  hb2135 : Goal L.ax-X2-K0-S0-CK10-CCK'=K0-CCK'-CCK'-X2-S0-S1-CS01-CS01-CS01-CS12-CS12
  hb2135 = ListNF.listnfeq' nf-p24k0d auto

  hb2136 : Goal L.ax-X2-K0-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12
  hb2136 = ListNF.listnfeq' nf-p24k0d auto

  hb2137 : Goal L.ax-X2-K0-S0-CK20=S0-K0-S0-CK20-X2-CX20-S0-S0-S2-S2-S2-CS02-CS02
  hb2137 = ListNF.listnfeq' nf-p24k0d auto

  hb2138 : Goal L.ax-X2-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-X2-CX10-CX20-CCX0-S0-S0-S2-S2-CS01-CS01-CS12-CS12-CCZ
  hb2138 = ListNF.listnfeq' nf-p24k0d auto

  hb2139 : Goal L.ax-X2-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X2-CX10-CX20-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CS12-CCZ
  hb2139 = ListNF.listnfeq' nf-p24k0d auto

  hb2140 : Goal L.ax-X2-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X2-CX20-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS02-CS02-CS12-CS12-CCZ
  hb2140 = ListNF.listnfeq' nf-p24k0d auto

  hb2141 : Goal L.ax-X2-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-X2-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02
  hb2141 = ListNF.listnfeq' nf-p24k0d auto

