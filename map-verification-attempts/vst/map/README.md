# Files

 * map.c - simiple array-based map int32 -> int32 map with a hardcoded capacity of 100 cells
 * map.v - clightgen-generated CompCert CoQ IR
 * map\_spec.v - FOL spec of map, a middle-level implementation in CoQ and an equivalence proof
 * map\_impl\_spec.v - A VST spec for the map.c functions, expressed through the intermediate implementation
 * verif\_map.v - A proof proof of map.v-to-map\_impl\_spec.v equivalence
