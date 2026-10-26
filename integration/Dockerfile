

ARG BASE=ubuntu:26.04
FROM ${BASE} AS upstream-plugins
RUN apt-get update \
 && apt-get install -y --no-install-recommends build-essential ca-certificates curl \
 && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL https://www.sudo.ws/dist/sudo-1.9.17p2.tar.gz -o /tmp/sudo.tar.gz \
 && echo '4a38a1ab3adb1199257edc2a7c4a2bd714665eb605b04368843b06dada2cfcfb  /tmp/sudo.tar.gz' | sha256sum -c - \
 && tar -xzf /tmp/sudo.tar.gz -C /tmp
WORKDIR /tmp/sudo-1.9.17p2
RUN ./configure --enable-static-sudoers --disable-shared-libutil --without-pam --without-ssl --disable-nls \
 && make -C lib/util \
 && make -C plugins/sample \
 && make -C plugins/sample_approval

FROM ${BASE}

ENV DEBIAN_FRONTEND=noninteractive LANG=C.UTF-8



RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      sudo sudo-rs python3 procps util-linux passwd login libpam-modules libpam-runtime \
      locales language-pack-de-base language-pack-fr-base strace openssl \
      slapd ldap-utils sssd sssd-ldap libsss-sudo libnss-sss rsyslog exim4-daemon-light \
      ssh-askpass xvfb xdotool openssh-server openssh-client libpam-oath oathtool cracklib-runtime \
 && rm -rf /var/lib/apt/lists/*
RUN localedef -i de_DE -f UTF-8 de_DE.UTF-8 \
 && localedef -i fr_FR -f UTF-8 fr_FR.UTF-8



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
COPY --from=upstream-plugins /tmp/sudo-1.9.17p2/plugins/sample/.libs/sample_plugin.so /opt/sudo-it/plugins/sample_plugin.so
COPY --from=upstream-plugins /tmp/sudo-1.9.17p2/plugins/sample_approval/.libs/sample_approval.so /opt/sudo-it/plugins/sample_approval.so

RUN printf '%s\n' 'dc_eximconfig_configtype='\''local'\''' \
      'dc_other_hostnames='\''example.test'\''' 'dc_local_interfaces='\''127.0.0.1'\''' \
      'dc_readhost='\'''\''' 'dc_relay_domains='\'''\''' 'dc_minimaldns='\''true'\''' \
      'dc_relay_nets='\'''\''' 'dc_smarthost='\'''\''' 'CFILEMODE='\''644'\''' \
      'dc_use_split_config='\''false'\''' 'dc_hide_mailname='\''false'\''' \
      'dc_mailname_in_oh='\''true'\''' 'dc_localdelivery='\''mail_spool'\''' \
      >/etc/exim4/update-exim4.conf.conf \
 && printf 'example.test\n' >/etc/mailname \
 && printf 'admin: root\n' >>/etc/aliases \
 && sed -i 's|data = /var/mail/mail|data = /var/mail/root|' /etc/exim4/exim4.conf.template \
 && update-exim4.conf
