
namespace Thunk

@[ext] theorem ext : {a b : Thunk α} → a.get = b.get → a = b
  | {..}, {..}, heq => congrArg _ <| funext fun _ => heq

end Thunk
