#!/usr/bin/env bash
#
# scripts/lib/topic-revset.sh
#
# Shared revset definitions for topic-branch bookmarks.
# Source this file from regenerate-integration.sh and
# rebase-topics.sh.
#
# Exports:
#   TOPIC_BOOKMARKS_REVSET — union of bookmark-glob revsets
#                            for every topic-branch prefix.
#   TOPIC_TIPS_NOT_ON_MAIN_REVSET — those tips minus ::main.

# shellcheck disable=SC2034  # consumed by sourcing scripts
TOPIC_BOOKMARKS_REVSET='bookmarks(glob:"feat/*") |
                        bookmarks(glob:"fix/*") |
                        bookmarks(glob:"refactor/*") |
                        bookmarks(glob:"migrate/*") |
                        bookmarks(glob:"chore/*") |
                        bookmarks(glob:"docs/*") |
                        bookmarks(glob:"bump/*")'

# shellcheck disable=SC2034
TOPIC_TIPS_NOT_ON_MAIN_REVSET='(bookmarks(glob:"feat/*") ~ ::main) |
                               (bookmarks(glob:"fix/*") ~ ::main) |
                               (bookmarks(glob:"refactor/*") ~ ::main) |
                               (bookmarks(glob:"migrate/*") ~ ::main) |
                               (bookmarks(glob:"chore/*") ~ ::main) |
                               (bookmarks(glob:"docs/*") ~ ::main) |
                               (bookmarks(glob:"bump/*") ~ ::main)'
