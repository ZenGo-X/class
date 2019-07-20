/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*******************************************************************/
/*                                                                 */
/*                 INTERFACE TO READLINE COMPLETION                */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/**************************************************************************/
static entree *current_ep = NULL;

/* do we add () at the end of completed word? (is it a function?) */
static int
add_paren(pari_rl_interface *rl, int end)
{
  entree *ep;
  const char *s;

  if (end < 0 || (*rl->line_buffer)[end] == '(')
    return 0; /* not from command_generator or already there */
  ep = do_alias(current_ep); /* current_ep set in command_generator */
  if (EpVALENCE(ep) < EpNEW)
  { /* is it a constant masked as a function (e.g Pi)? */
    s = ep->help; if (!s) return 1;
    while (is_keyword_char(*s)) s++;
    return (*s != '=');
  }
  switch(EpVALENCE(ep))
  {
    case EpVAR: return typ((GEN)ep->value) == t_CLOSURE;
    case EpINSTALL: return 1;
  }
  return 0;
}

static void
match_concat(char **matches, const char *s)
{
  matches[0] = (char*)pari_realloc((void*)matches[0],
                                strlen(matches[0])+strlen(s)+1);
  strcat(matches[0],s);
}

#define add_comma(x) (x==-2) /* from default_generator */

/* a single match, possibly modify matches[0] in place */
static void
treat_single(pari_rl_interface *rl, int code, char **matches)
{
  if (add_paren(rl, code))
  {
    match_concat(matches,"()");
    rl->back = 1;
    if (*rl->point == *rl->end)
    *rl->completion_append_character = '\0'; /* Do not append space. */
  }
  else if (add_comma(code))
    match_concat(matches,",");
}
#undef add_comma


static char **
matches_for_emacs(const char *text, char **matches)
{
  if (!matches) printf("@");
  else
  {
    int i;
    printf("%s@", matches[0] + strlen(text));
    if (matches[1]) print_fun_list(matches+1,0);

   /* we don't want readline to do anything, but insert some junk
    * which will be erased by emacs.
    */
    for (i=0; matches[i]; i++) pari_free(matches[i]);
    pari_free(matches);
  }
  matches = (char **) pari_malloc(2*sizeof(char *));
  matches[0] = (char*)pari_malloc(2); sprintf(matches[0],"_");
  matches[1] = NULL; printf("@E_N_D"); pari_flush();
  return matches;
}

/* Attempt to complete on the contents of TEXT. 'code' is used to
 * differentiate between callers when a single match is found.
 * Return the array of matches, NULL if there are none. */
static char **
get_matches(pari_rl_interface *rl, int code, const char *text, char *(*f)(const char*, int))
{
  char **matches = rl->completion_matches(text, f);
  if (matches && !matches[1]) treat_single(rl, code, matches);
  if (GP_DATA->flags & gpd_EMACS) matches = matches_for_emacs(text,matches);
  return matches;
}

static char *
add_prefix(const char *name, const char *text, long junk)
{
  char *s = strncpy((char*)pari_malloc(strlen(name)+1+junk),text,junk);
  strcpy(s+junk,name); return s;
}
static void
init_prefix(const char *text, int *len, int *junk, char **TEXT)
{
  long l = strlen(text), j = l-1;
  while (j >= 0 && is_keyword_char(text[j])) j--;
  if (j >= 7 && text[j] == '-' && !strncmp(text+(j-7),"refcard",7)) j -= 8;
  j++;
  *TEXT = (char*)text + j;
  *junk = j;
  *len  = l - j;
}

static int
is_internal(entree *ep) { return *ep->name == '_'; }

/* Generator function for command completion.  STATE lets us know whether
 * to start from scratch; without any state (i.e. STATE == 0), then we
 * start at the top of the list. */
static char *
hashtable_generator(const char *text, int state, entree **hash)
{
  static int hashpos, len, junk;
  static entree* ep;
  static char *TEXT;

 /* If this is a new word to complete, initialize now:
  *  + indexes hashpos (GP hash list) and n (keywords specific to long help).
  *  + file completion and keyword completion use different word boundaries,
  *    have TEXT point to the keyword start.
  *  + save the length of TEXT for efficiency.
  */
  if (!state)
  {
    hashpos = 0; ep = hash[hashpos];
    init_prefix(text, &len, &junk, &TEXT);
  }

  /* Return the next name which partially matches from the command list. */
  for(;;)
    if (!ep)
    {
      if (++hashpos >= functions_tblsz) return NULL; /* no names matched */
      ep = hash[hashpos];
    }
    else if (is_internal(ep) || strncmp(ep->name,TEXT,len))
      ep = ep->next;
    else
      break;
  current_ep = ep; ep = ep->next;
  return add_prefix(current_ep->name,text,junk);
}
/* Generator function for member completion.  STATE lets us know whether
 * to start from scratch; without any state (i.e. STATE == 0), then we
 * start at the top of the list. */
static char *
member_generator(const char *text, int state)
{
  static int hashpos, len, junk;
  static entree* ep;
  static char *TEXT;
  entree **hash=functions_hash;

 /* If this is a new word to complete, initialize now:
  *  + indexes hashpos (GP hash list) and n (keywords specific to long help).
  *  + file completion and keyword completion use different word boundaries,
  *    have TEXT point to the keyword start.
  *  + save the length of TEXT for efficiency.
  */
  if (!state)
  {
    hashpos = 0; ep = hash[hashpos];
    init_prefix(text, &len, &junk, &TEXT);
  }

  /* Return the next name which partially matches from the command list. */
  for(;;)
    if (!ep)
    {
      if (++hashpos >= functions_tblsz) return NULL; /* no names matched */
      ep = hash[hashpos];
    }
    else if (ep->name[0]=='_' && ep->name[1]=='.'
             && !strncmp(ep->name+2,TEXT,len))
        break;
    else
        ep = ep->next;
  current_ep = ep; ep = ep->next;
  return add_prefix(current_ep->name+2,text,junk);
}
static char *
command_generator(const char *text, int state)
{ return hashtable_generator(text,state, functions_hash); }
static char *
default_generator(const char *text,int state)
{ return hashtable_generator(text,state, defaults_hash); }

static char *
ext_help_generator(const char *text, int state)
{
  static int len, junk, n, def, key;
  static char *TEXT;
  if (!state) {
    n = 0;
    def = key = 1;
    init_prefix(text, &len, &junk, &TEXT);
  }
  if (def)
  {
    char *s = default_generator(TEXT, state);
    if (s) return add_prefix(s, text, junk);
    def = 0;
  }
  if (key)
  {
    const char **L = gphelp_keyword_list();
    for ( ; L[n]; n++)
      if (!strncmp(L[n],TEXT,len))
        return add_prefix(L[n++], text, junk);
    key = 0; state = 0;
  }
  return command_generator(text, state);
}

/* add a space between \<char> and following text. Attempting completion now
 * would delete char. Hitting <TAB> again will complete properly */
static char **
add_space(pari_rl_interface *rl, int start)
{
  char **m;
  int p = *rl->point + 1;
  *rl->point = start + 2;
  rl->insert(1, ' '); *rl->point = p;
  /*better: fake an empty completion, but don't append ' ' after it! */
  *rl->completion_append_character = '\0';
  m = (char**)pari_malloc(2 * sizeof(char*));
  m[0] = (char*)pari_malloc(1); *(m[0]) = 0;
  m[1] = NULL; return m;
}

char **
pari_completion(pari_rl_interface *rl, char *text, int START, int END)
{
  int i, first=0, start=START;
  char *line = *rl->line_buffer;

  *rl->completion_append_character = ' ';
  current_ep = NULL;
  while (line[first] && isspace((int)line[first])) first++;
  if (line[first] == '?')
  {
      if (line[first+1] == '?')
        return get_matches(rl, -1, text, ext_help_generator);
      return get_matches(rl, -1, text, command_generator);
  }

/* If the line does not begin by a backslash, then it is:
 * . an old command ( if preceded by "whatnow(" ).
 * . a default ( if preceded by "default(" ).
 * . a member function ( if preceded by "." + keyword_chars )
 * . a file name (in current directory) ( if preceded by 'read' or 'writexx' )
 * . a command */
  if (start >=1 && line[start] != '~') start--;
  while (start && is_keyword_char(line[start])) start--;
  if (line[start] == '~')
  {
    char *(*f)(const char*, int);
    f = rl->username_completion_function;
    for(i=start+1;i<=END;i++)
      if (line[i] == '/') { f = rl->filename_completion_function; break; }
    return get_matches(rl, -1, text, f);
  }
  if (line[first] == '\\')
  {
    if (first == start) return add_space(rl, start);
    return get_matches(rl, -1, text, rl->filename_completion_function);
  }

  while (start && line[start] != '('
               && line[start] != ',') start--;
  if (line[start] == '(' && start)
  {
    int iend, j,k;
    entree *ep;
    char buf[200];

    i = start;

    while (i && isspace((int)line[i-1])) i--;
    iend = i;
    while (i && is_keyword_char(line[i-1])) i--;

    if (strncmp(line + i,"default",7) == 0)
      return get_matches(rl, -2, text, default_generator);
    if ( strncmp(line + i,"read",4)  == 0
      || strncmp(line + i,"write",5) == 0)
      return get_matches(rl, -1, text, rl->filename_completion_function);

    j = start + 1;
    while (j <= END && isspace((int)line[j])) j++;
    k = END;
    while (k > j && isspace((int)line[k])) k--;
    /* If we are in empty parens, insert the default arguments */
    if ((GP_DATA->readline_state & DO_ARGS_COMPLETE) && k == j
         && (line[j] == ')' || !line[j])
         && (iend - i < (long)sizeof(buf))
         && ( strncpy(buf, line + i, iend - i),
              buf[iend - i] = 0, 1)
         && (ep = is_entry(buf)) && ep->help)
    {
      const char *s = ep->help;
      while (is_keyword_char(*s)) s++;
      if (*s++ == '(')
      { /* function call: insert arguments */
        const char *e = s;
        while (*e && *e != ')' && *e != '(') e++;
        if (*e == ')')
        { /* we just skipped over the arguments in short help text */
          char *str = strncpy((char*)pari_malloc(e-s + 1), s, e-s);
          char **ret = (char**)pari_malloc(sizeof(char*)*2);
          str[e-s] = 0;
          ret[0] = str; ret[1] = NULL;
          if (GP_DATA->flags & gpd_EMACS) ret = matches_for_emacs("",ret);
          return ret;
        }
      }
    }
  }
  for(i = END-1; i >= start; i--)
    if (!is_keyword_char(line[i]))
    {
      if (line[i] == '.')
        return get_matches(rl, -1, text, member_generator);
      break;
    }
  return get_matches(rl, END, text, command_generator);
}

static char *
pari_completion_word(char *line, long end)
{
  char *s = line + end, *found_quote = NULL;
  long i;
  *s = 0; /* truncate at cursor position */
  for (i=0; i < end; i++)
  { /* first look for unclosed string */
    switch(line[i])
    {
      case '"':
        found_quote = found_quote? NULL: line + i;
        break;
      case '\\': i++; break;
    }
  }
  if (found_quote) return found_quote + 1; /* return next char after quote */
  /* else find beginning of word */
  while (s > line && is_keyword_char(s[-1])) s--;
  return s;
}

char **
pari_completion_matches(pari_rl_interface *rl, const char *s, long pos, long *wordpos)
{
  char *text, *b;
  long w;

  if (*rl->line_buffer) pari_free(*rl->line_buffer);
  *rl->line_buffer = b = pari_strdup(s);
  text = pari_completion_word(b, pos);
  w = text - b; if (wordpos) *wordpos = w;
  /* text = start of expression we complete */
  *rl->end = strlen(b)-1;
  *rl->point = pos;
  return pari_completion(rl, text, w, pos);
}
