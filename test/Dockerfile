FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get install --yes --no-install-recommends bash coreutils python3 stow sudo && \
    rm --recursive --force /var/lib/apt/lists/*

ENV LANG=C.UTF-8
USER 1000:1000
WORKDIR /tmp
