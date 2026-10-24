import LeanSudo.Insults

/-! Compile-time checks for the full sudo 1.9.17p2 insult collection. -/
namespace Tests.Insults
open LeanSudo.Insults

-- All five groups, with their upstream ordering and boundary strings.
#guard messages.size == 60
#guard select 0 == "Just what do you think you're doing Dave?"
#guard select 7 == "I feel much better now."
#guard select 8 == "You silly, twisted boy you."
#guard select 30 == "I think ... err ... I think ... I think I'll go home"
#guard select 31 == "Wrong!  You cheating scum!"
#guard select 38 == "Your mind just hasn't been the same since the electro-shock, has it?"
#guard select 39 == "Maybe if you used more than just two fingers..."
#guard select 47 == "You speak an infinite deal of nothing"
#guard select 48 == "That is no basis for supreme executive power!"
#guard select 59 == "I'm very sorry, but I'm not allowed to argue unless you've paid."

-- Preserve unusual spelling, doubled spaces, and punctuation verbatim.
#guard select 20 == "There must be cure for it!"
#guard select 36 == "You type like i drive."
#guard select 40 == "BOB says:  You seem to have forgotten your passwd, enter another!"
#guard select 56 == "When you're walking home tonight, and some homicidal maniac comes after you with a bunch of loganberries, don't come crying to me!"
#guard select 57 == "This man, he doesn't know when he's beaten! He doesn't know when he's winning, either. He has no... sort of... sensory apparatus..."

-- Modulo selection wraps and supports seeds beyond native machine integers.
#guard select 60 == select 0
#guard select 119 == select 59
#guard select 120 == select 0
#guard select 18446744073709551616 == select 16
#guard (List.range 60).all (fun i => select i == messages[i]!)
#guard (List.range 60).all (fun i => select (i + 60) == select i)
#guard messages.all (fun message => !message.isEmpty && !message.contains '\n')

example (seed : Nat) : select seed ∈ messages := select_mem seed
example : 0 < messages.size := messages_nonempty

end Tests.Insults
