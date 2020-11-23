import sys
import os
import json
from google.oauth2 import service_account
from google.cloud import storage

credentials = service_account.Credentials.from_service_account_info(json.loads(os.environ['GOOGLE_CLOUD_PLATFORM_CREDENTIALS']))

storageClient = storage.Client(credentials.project_id, credentials)

bucket = storageClient.bucket('verifast-nightlies')

vfversion = os.environ['VFVERSION']

OS = os.environ['VERIFAST_OS']
if OS == 'Windows_NT':
  os_tag = 'windows'
  local_prefix = 'src/'
  suffix = '.zip'
elif OS == 'Darwin':
  os_tag = 'macos'
  local_prefix = 'src/upload/'
  suffix = '-osx.tar.gz'
else:
  local_prefix = 'src/upload/'
  os_tag = 'linux'
  suffix = '.tar.gz'

prefix = 'latest/' + os_tag + '/'

old_nightlies = list(storageClient.list_blobs(bucket, prefix=prefix))

local_filename = local_prefix + 'verifast-nightly' + suffix
object_filename = 'verifast-' + vfversion + suffix
new_nightly = bucket.blob(prefix + object_filename)
print('Uploading {} to {}...'.format(local_filename, new_nightly.name))
new_nightly.upload_from_filename(local_filename)
print('Uploaded {} to {}.'.format(local_filename, new_nightly.name))

html = """\
<html>
  <head>
    <meta http-equiv="refresh" content="0; URL={}" />
  </head>
</html>
""".format(prefix + object_filename)

html_object_filename = 'verifast-nightly-{}-latest.html'.format(os_tag)
print('Updating {}...'.format(html_object_filename))
bucket.blob(html_object_filename).upload_from_string(html, content_type='text/html')
print('Updated {}'.format(html_object_filename))

if old_nightlies:
    print('Deleting old nightlies {}'.format(old_nightlies))
    for old_nightly in old_nightlies:
        if old_nightly.name != new_nightly.name:
            old_nightly.delete()
            print('Deleted {}'.format(old_nightly.name))

