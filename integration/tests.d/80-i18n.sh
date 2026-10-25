



i18n_compare_reference() {
  local user=$1 command=$2 status=$3
  run "$user" "$command"
  expect_rc "$status"
  local actual_rc=$RC actual_out=$OUT actual_err=$ERR actual_cmd=$CMD
  cp "$WORK/out" "$WORK/i18n-actual-out"
  cp "$WORK/err" "$WORK/i18n-actual-err"
  run "$user" 'sudo() { /bin/bash -c '\''exec -a sudo /usr/bin/sudo.ws "$@"'\'' -- "$@"; }; '"$command"
  expect_rc "$status"
  diff -u "$WORK/i18n-actual-out" "$WORK/out" >>"$LOG" || fail 'stdout differs byte-for-byte from sudo.ws'
  diff -u "$WORK/i18n-actual-err" "$WORK/err" >>"$LOG" || fail 'stderr differs byte-for-byte from sudo.ws'
  RC=$actual_rc OUT=$actual_out ERR=$actual_err CMD=$actual_cmd
}

i18n_no_lecture() {
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-i18n <<'EOF'
Defaults lecture=never
EOF
}




begin i18n-de-password-prompt && {
  i18n_no_lecture
  XENV=(LANG=de_DE.UTF-8)
  i18n_compare_reference alice "printf 'alicepw\n' | sudo -kS /usr/bin/true" 0
  expect_out_empty
  [[ $ERR == '[sudo] Passwort für alice: ' ]] || fail 'German password prompt differs'
  end
}

begin i18n-de-wrong-password && {
  i18n_no_lecture
  XENV=(LANG=de_DE.UTF-8)
  i18n_compare_reference alice "printf 'wrong\nalicepw\n' | sudo -kS /usr/bin/true" 0
  expect_out_empty
  expect_err_has 'Das hat nicht funktioniert, bitte nochmal probieren.'
  expect_err_lacks 'Sorry, try again.'
  end
}

begin i18n-de-not-in-sudoers && {
  i18n_no_lecture
  XENV=(LANG=de_DE.UTF-8)
  i18n_compare_reference bob "printf 'bobpw\n' | sudo -kS /usr/bin/true" 1
  expect_out_empty
  expect_err_has '»bob« ist nicht in der sudoers-Datei.'
  end
}

begin i18n-de-list-header && {
  i18n_no_lecture
  XENV=(LANG=de_DE.UTF-8)
  i18n_compare_reference root 'sudo -l -U alice' 0
  expect_out_line 'Passende Defaults-Einträge für alice auf sudo-it:'
  expect_out_line 'Der Benutzer alice darf die folgenden Befehle auf sudo-it ausführen:'
  end
}

begin i18n-de-usage-error && {
  XENV=(LANG=de_DE.UTF-8)
  i18n_compare_reference alice 'sudo -i -s' 1
  expect_out_empty
  expect_err_has 'sudo: sie dürfen nicht gleichzeitig die -i und die -s Optionen setzen'

  expect_err_has 'usage: sudo -h | -K | -k | -V'
  end
}

begin i18n-de-help && {
  XENV=(LANG=de_DE.UTF-8)
  i18n_compare_reference alice 'sudo -h' 0
  expect_out_line 'sudo - Einen Befehl als anderer Benutzer ausführen'
  expect_out_line 'Optionen:'
  end
}



for i18n_case in password-prompt wrong-password not-in-sudoers list-header usage-error help; do
  begin "i18n-C-byte-unchanged-$i18n_case" && {
    i18n_no_lecture
    XENV=(LANG=C LANGUAGE=fr)
    case $i18n_case in
      password-prompt)
        i18n_compare_reference alice "printf 'alicepw\n' | sudo -kS /usr/bin/true" 0
        [[ $ERR == '[sudo] password for alice: ' ]] || fail 'C password prompt differs'
        ;;
      wrong-password)
        i18n_compare_reference alice "printf 'wrong\nalicepw\n' | sudo -kS /usr/bin/true" 0
        expect_err_has 'Sorry, try again.'
        ;;
      not-in-sudoers)
        i18n_compare_reference bob "printf 'bobpw\n' | sudo -kS /usr/bin/true" 1
        expect_err_has 'bob is not in the sudoers file.'
        ;;
      list-header)
        i18n_compare_reference root 'sudo -l -U alice' 0
        expect_out_line 'User alice may run the following commands on sudo-it:'
        ;;
      usage-error)
        i18n_compare_reference alice 'sudo -i -s' 1
        expect_err_has 'you may not specify both the -i and -s options'
        ;;
      help)
        i18n_compare_reference alice 'sudo -h' 0
        expect_out_line 'sudo - execute a command as another user'
        ;;
    esac
    end
  }
done



begin i18n-LANGUAGE-fr-password-precedence && {
  i18n_no_lecture
  XENV=(LANG=de_DE.UTF-8 LANGUAGE=fr)
  i18n_compare_reference alice "printf 'alicepw\n' | sudo -kS /usr/bin/true" 0
  [[ $ERR == '[sudo] Mot de passe de alice : ' ]] || fail 'French password prompt differs'
  end
}

begin i18n-LANGUAGE-fr-help-precedence && {
  XENV=(LANG=de_DE.UTF-8 LANGUAGE=fr)
  i18n_compare_reference alice 'sudo -h' 0
  expect_out_line "sudo – exécute une commande en tant qu'un autre utilisateur"
  end
}

begin i18n-missing-locale-password-english && {
  i18n_no_lecture
  XENV=(LANG=zz_ZZ.UTF-8)
  i18n_compare_reference alice "printf 'alicepw\n' | sudo -kS /usr/bin/true" 0
  [[ $ERR == '[sudo] password for alice: ' ]] || fail 'Missing locale did not use English prompt'
  end
}

begin i18n-missing-locale-help-english && {
  XENV=(LANG=zz_ZZ.UTF-8)
  i18n_compare_reference alice 'sudo -h' 0
  expect_out_line 'sudo - execute a command as another user'
  end
}

begin i18n-configured-passprompt-untranslated && {
  i18n_no_lecture
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-i18n-custom <<'EOF'
Defaults:alice passprompt="Admin password for %p: "
EOF
  XENV=(LANG=de_DE.UTF-8)
  i18n_compare_reference alice "printf 'alicepw\n' | sudo -kS /usr/bin/true" 0
  [[ $ERR == 'Admin password for alice: ' ]] || fail 'Configured prompt changed beyond %p expansion'
  end
}

begin i18n-configured-badpass-untranslated && {
  i18n_no_lecture


  install -m 0440 /dev/stdin /etc/sudoers.d/zz-i18n-custom <<'EOF'
Defaults:alice badpass_message="Sorry, try again."
EOF
  XENV=(LANG=de_DE.UTF-8)
  i18n_compare_reference alice "printf 'wrong\nalicepw\n' | sudo -kS /usr/bin/true" 0
  expect_err_has '[sudo] Passwort für alice: '
  expect_err_has 'Sorry, try again.'
  expect_err_lacks 'Das hat nicht funktioniert, bitte nochmal probieren.'
  end
}
