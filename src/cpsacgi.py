#! /usr/bin/python

"""Warning: this CGI script is for deployment in friendly
environments only!"""

import cgi
import sys
import subprocess
import cgitb; cgitb.enable()

# The command used to start cpsa limits memory usage
cpsa_command = ['./cpsa', '+RTS', '-M512m', '-RTS']
# Flag for using ps to determine if a copy of cpsa is already running
use_in_use_check = False

def main():
    shapes_cmd = './cpsashapes'
    graph_cmd = './cpsagraph -c'
    annotations_cmd = './cpsaannotations'
    xml_cmd = './cpsagraph -x'
    shapes_graph_cmd = shapes_cmd + ' | ' + graph_cmd
    shapes_xml_cmd = shapes_cmd + ' | ' + xml_cmd
    shapes_annotations_cmd = shapes_cmd + ' | ' + annotations_cmd
    shapes_annotations_xml_cmd = shapes_annotations_cmd + ' | ' + xml_cmd
    form = cgi.FieldStorage()
    if form.has_key('xml'):
        resp = xml(xml_cmd, form['xml'], None)
    elif form.has_key('shapes xml'):
        resp = xml(shapes_xml_cmd, form['shapes xml'], None)
    elif form.has_key('shapes annotations xml'):
        resp = xml(shapes_annotations_xml_cmd,
                   form['shapes annotations xml'], None)
    elif form.has_key('graph'):
        resp = graph(graph_cmd, form['graph'], None)
    elif form.has_key('shapes graph'):
        resp = graph(shapes_graph_cmd, form['shapes graph'], None)
    elif form.has_key('cpsa'):
        resp = cpsa(None, form['cpsa'])
    elif form.has_key('cpsa shapes'):
        resp = cpsa(shapes_cmd, form['cpsa shapes'])
    elif form.has_key('cpsa shapes annotations'):
        resp = cpsa(shapes_annotations_cmd,
                    form['cpsa shapes annotations'])
    elif form.has_key('cpsa xml'):
        resp = cpsa_xml(xml_cmd, form['cpsa xml'])
    elif form.has_key('cpsa shapes xml'):
        resp = cpsa_xml(shapes_xml_cmd, form['cpsa shapes xml'])
    elif form.has_key('cpsa shapes annotations xml'):
        resp = cpsa_xml(shapes_annotations_xml_cmd,
                        form['cpsa shapes annotations xml'])
    elif form.has_key('cpsa graph'):
        resp = cpsa_graph(graph_cmd, form['cpsa graph'])
    elif form.has_key('cpsa shapes graph'):
        resp = cpsa_graph(shapes_graph_cmd, form['cpsa shapes graph'])
    else:
        resp = 'Content-Type: text/plain\n\nBad form input\n'
    sys.stdout.write(resp)

def graph(command, data, source):
    if not source and not data.file:
        return 'Content-Type: text/plain\n\nBad form input--no file\n'
    p = subprocess.Popen(command, shell=True, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if source:
        p.stdin.write(source)
    else:
        p.stdin.write(data.value)
    p.stdin.close()
    out = bounded_read(p.stdout)
    err = p.stderr.read()
    if p.wait():
        resp = 'Content-Type: text/plain\n\n' + err
    elif not out:
        resp = 'Content-Type: text/plain\n\nSize limit exceeded'
    else:
        resp = 'Content-Type: image/svg+xml; charset=UTF-8\n'
        if source and data.filename: # Add content disposition
            name = data.filename
            i = name.rfind('.')
            if i > 0:
                name = name[0:i]
            fmt = 'Content-Disposition: attachment; filename=%s.svg\n\n'
            resp += fmt % name
        else:
            resp += '\n'
        resp += out
    return resp

def xml(command, data, source):
    if not source and not data.file:
        return 'Content-Type: text/plain\n\nBad form input--no file\n'
    p = subprocess.Popen(command, shell=True, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if source:
        p.stdin.write(source)
    else:
        p.stdin.write(data.value)
    p.stdin.close()
    out = bounded_read(p.stdout)
    err = p.stderr.read()
    if p.wait():
        resp = 'Content-Type: text/plain\n\n' + err
    elif not out:
        resp = 'Content-Type: text/plain\n\nSize limit exceeded'
    else:
        resp = 'Content-Type: text/xml; charset=UTF-8\n\n' + out
    return resp

def cpsa(command, data):
    global cpsa_command
    resp = 'Content-Type: text/plain; charset=US-ASCII\n\n'
    if not data.file:
        resp += 'Bad form input--no file\n'
        return resp
    busy = in_use()
    if busy:
        return busy
    p = subprocess.Popen(cpsa_command, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p.stdin.write(data.value)
    p.stdin.close()
    out = bounded_read(p.stdout)
    err = p.stderr.read()
    if p.wait():
        return resp + err
    elif not out:
        return resp + 'Size limit exceeded'
    elif not command:
        return resp + out
    p = subprocess.Popen(command, shell=True, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p.stdin.write(out)
    p.stdin.close()
    out = bounded_read(p.stdout)
    err = p.stderr.read()
    if p.wait():
        return resp + err
    elif not out:
        return resp + 'Size limit exceeded'
    else:
        return resp + out

def cpsa_graph(command, data):
    global cpsa_command
    if not data.file:
        resp = 'Content-Type: text/plain; charset=US-ASCII\n\n'
        resp += 'Bad form input--no file\n'
        return resp
    busy = in_use()
    if busy:
        return busy
    p = subprocess.Popen(cpsa_command, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p.stdin.write(data.value)
    p.stdin.close()
    out = bounded_read(p.stdout)
    err = p.stderr.read()
    if p.wait():
        resp = 'Content-Type: text/plain; charset=US-ASCII\n\n' + err
        return resp
    if not out:
        resp = 'Content-Type: text/plain\n\nSize limit exceeded'
        return resp
    resp = 'Content-Type: multipart/mixed; boundary="boundary"'
    resp += '\n\n--boundary\n'
    resp += graph(command, data, out)
    resp += '\n--boundary\n'
    resp += 'Content-Type: text/plain; charset=US-ASCII\n\n'
    resp += out
    resp += '\n--boundary--\n'
    return resp

def cpsa_xml(command, data):
    global cpsa_command
    if not data.file:
        resp = 'Content-Type: text/plain; charset=US-ASCII\n\n'
        resp += 'Bad form input--no file\n'
        return resp
    busy = in_use()
    if busy:
        return busy
    p = subprocess.Popen(cpsa_command, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p.stdin.write(data.value)
    p.stdin.close()
    out = bounded_read(p.stdout)
    err = p.stderr.read()
    if p.wait():
        resp = 'Content-Type: text/plain; charset=US-ASCII\n\n' + err
        return resp
    if not out:
        resp = 'Content-Type: text/plain\n\nSize limit exceeded'
        return resp
    return xml(command, data, out)

# Use ps to ensure at most one copy of cpsa is running.
def in_use():
    global use_in_use_check
    if not use_in_use_check:
        return False
    p = subprocess.Popen(['ps', '-ux'], stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p.stdin.close()
    out = p.stdout.read()
    err = p.stderr.read()
    if p.wait():
        resp = 'Content-Type: text/plain; charset=US-ASCII\n\n' + err
        return resp
    if out.find("cpsa") >= 0:
        return 'Content-Type: text/plain\n\nServer busy'
    return False

READ_BOUND = 2 << 20

# Return the empty string when the input is too big.
def bounded_read(f):
    buf = f.read(READ_BOUND)
    if f.read(1):
        return ""
    return buf

main()
