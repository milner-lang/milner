module type OrderedType = Map.OrderedType

module Make(Ord : OrderedType) = struct
  module Map = Map.Make(Ord)

  type 'a t = {
      bindings : 'a Map.t;
      parent : 'a t option;
    }

  let empty = { bindings = Map.empty; parent = None }

  let extend bindings parent = { bindings; parent = Some parent }

  let rec find k t =
    match Map.find_opt k t.bindings with
    | Some a -> Some a
    | None -> Option.bind t.parent (find k)
end
