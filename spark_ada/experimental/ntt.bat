:l ntt.cry

:! printf "\nProve naive NTT inverts.\n"
:prove naive_ntt_inverts
:! printf "\nProve naive Inverse NTT inverts.\n"
:prove naive_invntt_inverts

:! printf "\nProve fast NTT inverts.\n"
:prove fast_ntt_inverts
:! printf "\nProve fast Inverse NTT inverts.\n"
:prove fast_invntt_inverts

:! printf "\nProve naive NTT equivalent to fast NTT.\n"
:prove naive_fast_ntt_equiv
:! printf "\nProve naive Inverse NTT equivalent to fast Inverse NTT.\n"
:prove naive_fast_invntt_equiv
