open Core
open Fspec_api
open Ir

val build_ir: fun_spec String.Map.t ->
              string ->
              string ->
              string ->
              string ->
              string ->
              string ->
              ir
