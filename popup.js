// popup.js - DealPal (scan + prevent duplicates + delete X)
// Full file — replace your existing popup.js with this.

document.addEventListener('DOMContentLoaded', () => {
  const scanBtn = document.getElementById('scanBtn');
  const trackedList = document.getElementById('trackedList');
  const consentCheckbox = document.getElementById('consent');
  const lastSeenDiv = document.getElementById('lastSeen');

  // Utility: safely normalize storage data to an array of items
  function normalizeStoredItems(data) {
    if (!data) return [];
    if (Array.isArray(data)) return data;
    if (typeof data === 'object') {
      try {
        return Object.keys(data).map(k => data[k]);
      } catch (e) {
        return [];
      }
    }
    return [];
  }

  // Load and render stored items + consent
  function loadAll() {
    chrome.storage.local.get(['trackedItems','tracked_items','share_consent'], (data) => {
      let items = [];
      if (data.trackedItems) items = normalizeStoredItems(data.trackedItems);
      else if (data.tracked_items) items = normalizeStoredItems(data.tracked_items);
      else items = [];

      renderTracked(items);
      consentCheckbox.checked = !!data.share_consent;
    });
  }

  // Render the tracked items list
  function renderTracked(items) {
    trackedList.innerHTML = '';
    if (!items || items.length === 0) {
      trackedList.innerHTML = '<div class="no-items">No tracked items yet.</div>';
      return;
    }

    items.forEach(item => {
      const node = document.createElement('div');
      node.className = 'item';
      const title = escapeHtml(item.title || item.url || 'Unknown product');
      const priceDisplay = item.priceText ? escapeHtml(item.priceText) : 'Price not detected';

      node.innerHTML = `
        <div style="display:flex;justify-content:space-between;align-items:center;">
          <div style="flex:1;min-width:0;">
            <div style="font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">${title}</div>
            <div class="small">Latest: ${priceDisplay}</div>
            <div style="margin-top:4px;"><a href="${item.url}" target="_blank" rel="noopener noreferrer">View product</a></div>
          </div>
          <div style="margin-left:8px;">
            <button class="deleteBtn" data-url="${item.url}" title="Delete" style="background:#e74c3c;border:none;color:white;padding:4px 7px;border-radius:3px;cursor:pointer;">X</button>
          </div>
        </div>
      `;

      trackedList.appendChild(node);
    });

    // attach delete handlers
    Array.from(trackedList.querySelectorAll('.deleteBtn')).forEach(btn => {
      btn.addEventListener('click', (e) => {
        const url = e.currentTarget.getAttribute('data-url');
        deleteTrackedByUrl(url);
      });
    });
  }

  // Save array to storage (writes to trackedItems key)
  function saveTrackedArray(arr, cb) {
    chrome.storage.local.set({ trackedItems: arr }, () => {
      if (typeof cb === 'function') cb();
    });
  }

  // Delete item by URL and clear duplicate message
  function deleteTrackedByUrl(url) {
    chrome.storage.local.get(['trackedItems','tracked_items'], (data) => {
      let items = [];
      if (data.trackedItems) items = normalizeStoredItems(data.trackedItems);
      else if (data.tracked_items) items = normalizeStoredItems(data.tracked_items);
      else items = [];

      const filtered = items.filter(i => i.url !== url);
      saveTrackedArray(filtered, () => {
        renderTracked(filtered);
        // Clear any duplicate / info message that might have been shown earlier
        lastSeenDiv.textContent = '';
      });
    });
  }

  // Prevent duplicates by URL (or title fallback)
  function isDuplicate(product, items) {
    if (!items || !items.length) return false;
    return items.some(i => (i.url && product.url && i.url === product.url) || (i.title && product.title && i.title === product.title));
  }

  // Sanitize for display
  function escapeHtml(text) {
    if (!text) return '';
    return String(text).replace(/[&<>"'`]/g, s => {
      const map = {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;','`':'&#96;'};
      return map[s];
    });
  }

  // Main scan action: inject a function to read page info and return it
  async function scanActiveTab() {
    try {
      const tabs = await chrome.tabs.query({ active: true, currentWindow: true });
      if (!tabs || tabs.length === 0) {
        lastSeenDiv.textContent = 'No active tab found.';
        return;
      }
      const tab = tabs[0];

      const results = await chrome.scripting.executeScript({
        target: { tabId: tab.id },
        func: function getProductInfo() {
          try {
            const titleSelectors = ['#productTitle','h1','[data-testid="product-title"]','[itemprop="name"]','.prod-ProductTitle','.product-title'];
            let title = '';
            for (const sel of titleSelectors) {
              const el = document.querySelector(sel);
              if (el && el.innerText && el.innerText.trim().length) {
                title = el.innerText.trim();
                break;
              }
            }
            if (!title) title = document.title || '';

            const priceSelectors = [
              '#priceblock_ourprice',
              '#priceblock_dealprice',
              '#priceblock_saleprice',
              '#price_inside_buybox',
              '.a-price .a-offscreen',
              '[itemprop="price"]',
              '.price', '.prod-Price', '.price-characteristic', '.priceblock_ourprice_lbl'
            ];
            let priceText = null;
            for (const sel of priceSelectors) {
              const el = document.querySelector(sel);
              if (el && (el.innerText || el.textContent)) {
                priceText = (el.innerText || el.textContent).trim();
                if (priceText) break;
              }
            }

            const numeric = priceText ? parseFloat(priceText.replace(/[^\d.]/g, '')) : null;

            return { title: title, priceText: priceText || null, price: isNaN(numeric) ? null : numeric, url: location.href, ts: Date.now() };
          } catch (err) {
            return { title: document.title || '', priceText: null, price: null, url: location.href, ts: Date.now() };
          }
        }
      });

      if (!results || !results[0] || !results[0].result) {
        lastSeenDiv.textContent = 'No product information returned from page.';
        return;
      }
      const product = results[0].result;

      // immediate feedback
      lastSeenDiv.textContent = `Scanned: ${product.title ? product.title.substring(0,60) : product.url}`;

      chrome.storage.local.get(['trackedItems','tracked_items'], (data) => {
        let items = [];
        if (data.trackedItems) items = normalizeStoredItems(data.trackedItems);
        else if (data.tracked_items) items = normalizeStoredItems(data.tracked_items);
        else items = [];

        if (isDuplicate(product, items)) {
          lastSeenDiv.textContent = 'This page is already tracked. Delete first to add again.';
          return;
        }

        items.unshift(product);
        saveTrackedArray(items, () => {
          renderTracked(items);
          lastSeenDiv.textContent = 'Added to tracked items';
        });
      });

    } catch (err) {
      console.error('scanActiveTab error', err);
      lastSeenDiv.textContent = 'Scan failed. See console.';
    }
  }

  // Wire up scan button
  scanBtn.addEventListener('click', () => {
    scanActiveTab();
  });

  // Consent toggle
  consentCheckbox.addEventListener('change', () => {
    chrome.storage.local.set({ share_consent: consentCheckbox.checked });
  });

  // initialize UI
  loadAll();
});
