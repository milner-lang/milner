type 'a t = 'a list -> 'a list

let append lhs rhs list = lhs (rhs list)

let empty list = list

let singleton x list = x :: list

let to_list t = t []
