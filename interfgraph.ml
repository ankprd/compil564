type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map

let make livGraph : igraph = Register.M.empty