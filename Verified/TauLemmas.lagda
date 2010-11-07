import Level
open import Common

module Verified.TauLemmas (∣Heap∣ : ℕ) where

import Verified.Heap
private module Heap = Verified.Heap ∣Heap∣
open Heap

import Verified.Action
private module Action = Verified.Action ∣Heap∣
open Action

import Verified.Language
private module Language = Verified.Language ∣Heap∣
open Language

open RawFunctor Action.rawFunctor

