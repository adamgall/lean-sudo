# End-to-end test image for sudo implementations (see integration/README.md).
# Build context: the integration/ directory.
ARG BASE=ubuntu:26.04
FROM ${BASE}

ENV DEBIAN_FRONTEND=noninteractive LANG=C.UTF-8

# sudo     -> original sudo.ws, installed as /usr/bin/sudo.ws (the reference)
# sudo-rs  -> /usr/lib/cargo/bin/sudo (Ubuntu's default `sudo` since 25.10)
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      sudo sudo-rs python3 procps util-linux passwd login libpam-modules libpam-runtime \
      locales language-pack-de-base language-pack-fr-base strace \
      slapd ldap-utils sssd sssd-ldap libsss-sudo libnss-sss \
 && rm -rf /var/lib/apt/lists/*
RUN localedef -i de_DE -f UTF-8 de_DE.UTF-8 \
 && localedef -i fr_FR -f UTF-8 fr_FR.UTF-8

# Test users. alice is in the stock `%sudo` rule; the others get rules from
# /etc/sudoers.d (fixtures below). bob has no sudo rights at all.
RUN set -eu; \
    for u in alice bob carol dave erin frank gina henry ivan judy kate liam mona nick olga pete; do useradd -m -s /bin/bash "$u"; done; \
    usermod -aG sudo alice; \
    printf '%s\n' alice:alicepw bob:bobpw carol:carolpw dave:davepw erin:erinpw frank:frankpw gina:ginapw henry:henrypw \
      ivan:ivanpw judy:judypw kate:katepw liam:liampw mona:monapw nick:nickpw olga:olgapw pete:petepw \
      | chpasswd

COPY sudoers.d/ /opt/sudo-it/sudoers.d/
RUN set -eu; \
    for f in /opt/sudo-it/sudoers.d/*; do \
      install -o root -g root -m 0440 "$f" "/etc/sudoers.d/$(basename "$f")"; \
    done; \
    /usr/sbin/visudo.ws -c

COPY ptyrun.py tests.sh /opt/sudo-it/
COPY tests.d/ /opt/sudo-it/tests.d/
COPY sudo-schema.ldif /opt/sudo-it/sudo-schema.ldif
RUN chmod 0755 /opt/sudo-it/ptyrun.py /opt/sudo-it/tests.sh && mkdir -p /opt/impl

ENTRYPOINT ["/opt/sudo-it/tests.sh"]
